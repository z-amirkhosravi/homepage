module
public import MathResearch.Fueter.PolynomialCalculus

/-! EI1: the canonical harmonic polynomial numerator of every spatial kernel derivative. -/
@[expose] public section
noncomputable section
open scoped Quaternion Topology BigOperators ContDiff
open MvPolynomial Filter
namespace MathResearch.Fueter

/-- A scalar component commutes with a genuine real coordinate derivative. -/
theorem realCoord_coordPartial (k j : Fin 4) {f : ℍ → ℍ} {q : ℍ}
    (hf : DifferentiableAt ℝ f q) :
    realCoord k (coordPartial j f q) =
      fderiv ℝ (fun x => realCoord k (f x)) q (coordinateBasis j) := by
  have he := ((realCoord k).hasFDerivAt.comp q hf.hasFDerivAt)
  change HasFDerivAt (fun x => realCoord k (f x)) _ q at he
  rw [he.fderiv]
  rfl

/-- Differentiation of the polynomial-over-norm-square representation. -/
theorem numeratorStep_derivative (P : RealPoly4) (r : ℕ) (j : Fin 4)
    {q : ℍ} (hq : q ≠ 0) :
    fderiv ℝ (fun x => polyEval P x / Quaternion.normSq x ^ (r + 2)) q (coordinateBasis j) =
      polyEval (numeratorStep r j P) q / Quaternion.normSq q ^ (r + 3) := by
  have hn := ((polyEval_contDiff normSqPoly).differentiable (by simp) q).hasFDerivAt
  have hN : polyEval normSqPoly q ≠ 0 := by simpa using Quaternion.normSq_ne_zero.mpr hq
  have hi := (hasFDerivAt_inv hN).comp q hn
  have hp := ((polyEval_contDiff P).differentiable (by simp) q).hasFDerivAt
  have hd := hp.mul (hi.pow (r + 2))
  have he : (fun x => polyEval P x / Quaternion.normSq x ^ (r + 2)) =
      (fun x => polyEval P x * (polyEval normSqPoly x)⁻¹ ^ (r + 2)) := by
    funext x; simp [div_eq_mul_inv]
  change HasFDerivAt (fun x => polyEval P x * (polyEval normSqPoly x)⁻¹ ^ (r + 2)) _ q at hd
  rw [he, hd.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, polyEval_pderiv, pderiv_normSqPoly,
    polyEval_mul, polyEval_X, polyEval_normSq, nsmul_eq_mul, smul_eq_mul]
  simp only [numeratorStep, polyEval_sub, polyEval_mul, polyEval_C, polyEval_X,
    polyEval_normSq, polyEval_two, Function.comp_apply, Nat.cast_add, Nat.cast_ofNat,
    show r + 2 - 1 = r + 1 by omega]
  have hN' := Quaternion.normSq_ne_zero.mpr hq
  simp only [pow_add, pow_one, inv_pow]
  field_simp [hN']
  ring

@[simp] theorem polyEval_conjugatePoly (k : Fin 4) (q : ℍ) :
    polyEval (conjugatePoly k) q = realCoord k (star q) := by
  fin_cases k <;> simp [conjugatePoly, polyEval, realCoord_apply, coordinateBasis,
    QuaternionAlgebra.coe_basisOneIJK_repr]

/-- Every real component of every ordered kernel derivative has the constructed numerator. -/
theorem numeratorJet_represents (l : List (Fin 4)) (k : Fin 4) {q : ℍ} (hq : q ≠ 0) :
    realCoord k (iteratedPartial l kernel q) =
      polyEval (numeratorJet l k) q / Quaternion.normSq q ^ (l.length + 2) := by
  induction l generalizing q with
  | nil => simp [numeratorJet, iteratedPartial, kernel, div_eq_mul_inv, mul_comm]
  | cons j l ih =>
    have hf := ((contDiffOn_iteratedPartial isOpen_punctured kernel_smooth l).contDiffAt
      (isOpen_punctured.mem_nhds hq)).differentiableAt (by simp)
    change realCoord k (coordPartial j (iteratedPartial l kernel) q) = _
    rw [realCoord_coordPartial k j hf]
    have he : (fun x => realCoord k (iteratedPartial l kernel x)) =ᶠ[𝓝 q]
        (fun x => polyEval (numeratorJet l k) x / Quaternion.normSq x ^ (l.length + 2)) :=
      eventually_of_mem (isOpen_punctured.mem_nhds hq) (fun x hx => ih hx)
    rw [he.fderiv_eq, numeratorStep_derivative _ _ _ hq]
    simp [numeratorJet, Nat.add_assoc]

/-- The scalar version of EI1's representation, for every component. -/
theorem kernelNumerator_represents (ν : Fin 3 → ℕ) (k : Fin 4) {q : ℍ} (hq : q ≠ 0) :
    realCoord k (higherKernel ν q) =
      polyEval (kernelNumerator ν k) q / Quaternion.normSq q ^ ((∑ i, ν i) + 2) := by
  simpa only [higherKernel, multiIndexPartial_spatial, kernelNumerator,
    spatialDerivativeList_length] using numeratorJet_represents (spatialDerivativeList ν) k hq

/-- Assemble the four real numerator polynomials as a quaternion-valued function. -/
def harmonicNumerator (ν : Fin 3 → ℕ) (q : ℍ) : ℍ :=
  ∑ k : Fin 4, polyEval (kernelNumerator ν k) q • coordinateBasis k

@[simp] theorem harmonicNumerator_component (ν : Fin 3 → ℕ) (k : Fin 4) (q : ℍ) :
    realCoord k (harmonicNumerator ν q) = polyEval (kernelNumerator ν k) q := by
  simp only [harmonicNumerator, map_sum, map_smul, realCoord_basis, smul_eq_mul]
  simp

/-- EI1/v1: homogeneous harmonic numerator components, the actual kernel derivative,
    the initial numerator, and the recurrence in every spatial direction. -/
theorem EI1_v1 :
    (∀ (ν : Fin 3 → ℕ) (k : Fin 4),
      (kernelNumerator ν k).IsHomogeneous ((∑ i, ν i) + 1) ∧
      InnerProductSpace.HarmonicOnNhd (polyEval (kernelNumerator ν k)) Set.univ) ∧
    (∀ (ν : Fin 3 → ℕ) (q : ℍ), q ≠ 0 →
      higherKernel ν q = (Quaternion.normSq q ^ ((∑ i, ν i) + 2))⁻¹ • harmonicNumerator ν q) ∧
    (∀ q : ℍ, harmonicNumerator 0 q = star q) ∧
    (∀ (ν : Fin 3 → ℕ) (j : Fin 3) (k : Fin 4),
      kernelNumerator (ν + Pi.single j 1) k =
        normSqPoly * pderiv j.succ (kernelNumerator ν k) -
          C (2 * (((∑ i, ν i) : ℕ) : ℝ) + 4) * (X j.succ * kernelNumerator ν k)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ν k
    exact ⟨by simpa [kernelNumerator, spatialDerivativeList_length] using
      numeratorJet_homogeneous (spatialDerivativeList ν) k,
      polyEval_harmonic (numeratorJet_laplacian _ k)⟩
  · intro ν q hq
    apply coordinateBasis.repr.injective
    ext k
    change realCoord k _ = realCoord k _
    rw [map_smul, harmonicNumerator_component, kernelNumerator_represents ν k hq]
    simp [div_eq_mul_inv, mul_comm]
  · intro q
    apply coordinateBasis.repr.injective
    ext k
    change realCoord k _ = realCoord k _
    rw [harmonicNumerator_component]
    simp [kernelNumerator, spatialDerivativeList, numeratorJet]
  · intro ν j k
    rw [kernelNumerator_recurrence, numeratorStep]
    rw [show 2 * ((↑(∑ i, ν i) : ℝ) + 2) = 2 * (↑(∑ i, ν i) : ℝ) + 4 by ring]

end MathResearch.Fueter
