module
public import MathResearch.Fueter.HarmonicPolynomial

/-! Evaluating real multivariate polynomials on mathlib's real quaternion space. -/
@[expose] public section
noncomputable section
open scoped Quaternion Topology BigOperators ContDiff
open MvPolynomial
namespace MathResearch.Fueter

/-- The four real component projections, in the order `re, imI, imJ, imK`. -/
def realCoord (i : Fin 4) : ℍ →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp coordinateBasis.equivFunL.toContinuousLinearMap

@[simp] theorem realCoord_apply (i : Fin 4) (q : ℍ) :
    realCoord i q = coordinateBasis.repr q i := rfl

@[simp] theorem realCoord_basis (i j : Fin 4) :
    realCoord i (coordinateBasis j) = if i = j then 1 else 0 := by
  simp [realCoord_apply, Module.Basis.repr_self, Finsupp.single_apply, eq_comm]

/-- Evaluation in the standard four real coordinates of a quaternion. -/
def polyEval (P : RealPoly4) (q : ℍ) : ℝ := eval (coordinateBasis.repr q) P

@[simp] theorem polyEval_C (c : ℝ) (q : ℍ) : polyEval (C c) q = c := by simp [polyEval]
@[simp] theorem polyEval_X (i : Fin 4) (q : ℍ) : polyEval (X i) q = realCoord i q := by
  simp [polyEval]
@[simp] theorem polyEval_add (P Q : RealPoly4) (q : ℍ) :
    polyEval (P + Q) q = polyEval P q + polyEval Q q := by simp [polyEval]
@[simp] theorem polyEval_sub (P Q : RealPoly4) (q : ℍ) :
    polyEval (P - Q) q = polyEval P q - polyEval Q q := by simp [polyEval]
@[simp] theorem polyEval_two (q : ℍ) : polyEval 2 q = 2 := by simp [polyEval]
@[simp] theorem polyEval_mul (P Q : RealPoly4) (q : ℍ) :
    polyEval (P * Q) q = polyEval P q * polyEval Q q := by simp [polyEval]

theorem polyEval_C_fun (c : ℝ) : polyEval (C c) = fun _ => c := funext (polyEval_C c)
theorem polyEval_add_fun (P Q : RealPoly4) :
    polyEval (P + Q) = fun q => polyEval P q + polyEval Q q := funext (polyEval_add P Q)
theorem polyEval_mul_X_fun (P : RealPoly4) (i : Fin 4) :
    polyEval (P * X i) = fun q => polyEval P q * realCoord i q := by
  funext q; simp

@[fun_prop] theorem polyEval_contDiff (P : RealPoly4) : ContDiff ℝ ∞ (polyEval P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa only [polyEval_C_fun] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℍ => c))
  | add P Q hp hq => simpa only [polyEval_add_fun] using hp.add hq
  | mul_X P i hp => simpa only [polyEval_mul_X_fun] using hp.mul (realCoord i).contDiff

/-- Symbolic polynomial differentiation agrees with the actual Fréchet derivative. -/
theorem polyEval_pderiv (P : RealPoly4) (j : Fin 4) (q : ℍ) :
    fderiv ℝ (polyEval P) q (coordinateBasis j) = polyEval (pderiv j P) q := by
  induction P using MvPolynomial.induction_on with
  | C c => rw [polyEval_C_fun]; simp [polyEval]
  | add P Q hp hq =>
    have hdP := (polyEval_contDiff P).differentiable (by simp)
    have hdQ := (polyEval_contDiff Q).differentiable (by simp)
    simp only [polyEval_add_fun, fderiv_fun_add hdP.differentiableAt hdQ.differentiableAt,
      add_apply, hp, hq, map_add]
  | mul_X P i hp =>
    have hdP := (polyEval_contDiff P).differentiable (by simp)
    simp only [polyEval_mul_X_fun, fderiv_fun_mul hdP.differentiableAt
      (realCoord i).differentiableAt, add_apply, smul_apply,
      (realCoord i).fderiv, hp, smul_eq_mul, pderiv_mul]
    by_cases h : i = j
    · subst i; simp; ring
    · simp [pderiv_X_of_ne h, h, mul_comm]

@[simp] theorem polyEval_normSq (q : ℍ) : polyEval normSqPoly q = Quaternion.normSq q := by
  simp [polyEval, normSqPoly, Fin.sum_univ_succ, coordinateBasis,
    QuaternionAlgebra.coe_basisOneIJK_repr, Quaternion.normSq_def, pow_two, add_assoc]

theorem coordinateBasis_orthonormal : Orthonormal ℝ coordinateBasis := by
  rw [orthonormal_iff_ite]
  intro i j
  simp only [Quaternion.inner_def, coordinateBasis_eq]
  fin_cases i <;> fin_cases j <;> norm_num

/-- The standard quaternion basis, now equipped with its Euclidean orthonormality. -/
def quaternionOrthonormalBasis : OrthonormalBasis (Fin 4) ℝ ℍ :=
  coordinateBasis.toOrthonormalBasis coordinateBasis_orthonormal

@[simp] theorem quaternionOrthonormalBasis_apply (i : Fin 4) :
    quaternionOrthonormalBasis i = coordinateBasis i := by
  exact congrFun (Module.Basis.coe_toOrthonormalBasis _ _) i

/-- The algebraic polynomial Laplacian is the ordinary Euclidean Laplacian. -/
theorem polyEval_laplacian (P : RealPoly4) :
    Laplacian.laplacian (polyEval P) = polyEval (polyLaplacian P) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (polyEval P) quaternionOrthonormalBasis]
  funext q
  simp only [polyEval, polyLaplacian, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, quaternionOrthonormalBasis_apply]
  have hd : DifferentiableAt ℝ (fderiv ℝ (polyEval P)) q :=
    (((polyEval_contDiff P).contDiffOn.fderiv_of_isOpen (m := ∞) isOpen_univ
      (by simp)).contDiffAt (by simp)).differentiableAt (by simp)
  have hfun : (fun x => fderiv ℝ (polyEval P) x (coordinateBasis i)) =
      polyEval (pderiv i P) := funext (polyEval_pderiv P i)
  change fderiv ℝ (fderiv ℝ (polyEval P)) q (coordinateBasis i) (coordinateBasis i) =
    polyEval (pderiv i (pderiv i P)) q
  rw [← polyEval_pderiv (pderiv i P) i q, ← hfun,
    fderiv_clm_apply hd (differentiableAt_const (coordinateBasis i))]
  simp

theorem polyEval_harmonic {P : RealPoly4} (hP : polyLaplacian P = 0) :
    InnerProductSpace.HarmonicOnNhd (polyEval P) Set.univ := by
  intro q _
  refine ⟨(polyEval_contDiff P).contDiffAt.of_le (by simp), ?_⟩
  rw [polyEval_laplacian, hP]
  exact Filter.Eventually.of_forall (fun x => by simp [polyEval])

end MathResearch.Fueter
