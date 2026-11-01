module
public import MathResearch.Spinor.QuaternionMatrix
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Algebra.MvPolynomial.Basic

/-! Smoothness and derivatives for varying polynomial representations. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Quaternion BigOperators Matrix.Norms.Elementwise ContDiff
open MvPolynomial
namespace MathResearch.Spinor

instance (n : ℕ) : FiniteDimensional ℝ (BinaryForm n) :=
  Module.Finite.trans ℂ (BinaryForm n)

theorem contDiff_polynomialAction_coeff (p : ComplexPoly2) (d : Fin 2 →₀ ℕ) :
    ContDiff ℝ ∞ (fun M : Matrix2 => (polynomialAction M p).coeff d) := by
  induction p using MvPolynomial.induction_on generalizing d with
  | C z => simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : Matrix2 => (C z : ComplexPoly2).coeff d))
  | add p q hp hq => simpa using (hp d).add (hq d)
  | mul_X p i hp =>
    simp only [map_mul, polynomialAction_X, coeff_mul]
    apply ContDiff.sum
    intro a _
    apply (hp a.1).mul
    simp [substitution]
    fun_prop

/-- A continuous real coefficient chart for the weighted polynomial norm. -/
def realCoefficientEquiv (n : ℕ) : BinaryForm n ≃L[ℝ] (Fin (n + 1) → ℂ) :=
  ((coefficientEquiv n).restrictScalars ℝ).toContinuousLinearEquiv

theorem contDiff_polynomialRepresentation_fixed (n : ℕ) (p : BinaryForm n) :
    ContDiff ℝ ∞ (fun M : Matrix2 => polynomialRepresentation n M p) := by
  have h : ContDiff ℝ ∞ (fun M : Matrix2 => realCoefficientEquiv n (polynomialRepresentation n M p)) := by
    apply contDiff_pi.mpr
    intro k
    exact contDiff_polynomialAction_coeff p (exponent n k)
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using
    (realCoefficientEquiv n).symm.contDiff.comp h

/-- The usual monomial basis element X^(n-k)Y^k. -/
def monomialForm (n : ℕ) (k : Fin (n + 1)) : BinaryForm n :=
  ⟨monomial (exponent n k) 1, isHomogeneous_monomial 1 (exponent_degree n k)⟩

theorem monomialForm_expansion (n : ℕ) (p : BinaryForm n) :
    ∑ k, (coefficients n p k) • monomialForm n k = p := by
  apply coefficients_injective n
  ext k
  simp [coefficients, monomialForm, coeff_monomial, (exponent_injective n).eq_iff]

/-- Smoothness in both the matrix and the polynomial, not just along linear paths. -/
theorem contDiff_polynomialRepresentation (n : ℕ) :
    ContDiff ℝ ∞ (fun z : Matrix2 × BinaryForm n => polynomialRepresentation n z.1 z.2) := by
  have he (z : Matrix2 × BinaryForm n) : polynomialRepresentation n z.1 z.2 =
      ∑ k, (coefficients n z.2 k) • polynomialRepresentation n z.1 (monomialForm n k) := by
    conv_lhs => rw [← monomialForm_expansion n z.2]
    simp
  simp_rw [he]
  apply ContDiff.sum
  intro k _
  apply ContDiff.fun_smul
  · exact (contDiff_apply ℝ (fun _ : Fin (n+1) => ℂ) k).comp ((realCoefficientEquiv n).contDiff.comp contDiff_snd)
  · exact (contDiff_polynomialRepresentation_fixed n (monomialForm n k)).comp contDiff_fst

/-- The quaternion matrix embedding as a real continuous linear map. -/
def quaternionMatrixCLM : ℍ →L[ℝ] Matrix2 :=
  LinearMap.toContinuousLinearMap
    { toFun := quaternionMatrix
      map_add' := quaternionMatrix_add
      map_smul' := by
        intro r q
        apply Matrix.ext; intro i j
        fin_cases i <;> fin_cases j <;> simp [quaternionMatrix] <;> ring }

@[simp] theorem quaternionMatrixCLM_apply (q : ℍ) : quaternionMatrixCLM q = quaternionMatrix q := rfl

/-- Smoothness in the quaternion and polynomial, via the actual matrix embedding. -/
theorem contDiff_quaternionPolynomialRepresentation (n : ℕ) :
    ContDiff ℝ ∞ (fun z : ℍ × BinaryForm n => polynomialRepresentation n (quaternionMatrix z.1) z.2) := by
  have hq : ContDiff ℝ ∞ (fun z : ℍ × BinaryForm n => quaternionMatrixCLM z.1) :=
    quaternionMatrixCLM.contDiff.comp (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : ℍ × BinaryForm n → ℍ))
  have hpair : ContDiff ℝ ∞ (fun z : ℍ × BinaryForm n => (quaternionMatrixCLM z.1, z.2)) :=
    hq.prodMk (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℍ × BinaryForm n → BinaryForm n))
  simpa only [Function.comp_def, quaternionMatrixCLM_apply] using
    (contDiff_polynomialRepresentation n).comp hpair

/-- The real derivative at 1, now as a Fréchet derivative in arbitrary directions. -/
theorem fderiv_quaternionPolynomialRepresentation_one (m : ℕ) (p : BinaryForm (m+1)) (v : ℍ) :
    fderiv ℝ (fun a => polynomialRepresentation (m+1) (quaternionMatrix a) p) 1 v =
      infinitesimalAction m (quaternionMatrix v) p := by
  have hf : DifferentiableAt ℝ (fun a => polynomialRepresentation (m+1) (quaternionMatrix a) p) 1 :=
    ((contDiff_quaternionPolynomialRepresentation (m+1)).comp
      (contDiff_id.prodMk (contDiff_const (c := p)))).differentiable (by simp) 1
  have hpath : HasDerivAt (fun t : ℝ => 1 + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (1 : ℍ)
  have h := (show HasFDerivAt (fun a => polynomialRepresentation (m+1) (quaternionMatrix a) p) _ ((fun t : ℝ => 1 + t • v) 0) from (by simpa using hf.hasFDerivAt)).comp_hasDerivAt 0 hpath
  simpa using h.unique (quaternionPolynomialRepresentation_hasDerivAt m v p)

/-- The joint derivative at the identity: dτ(v)p + p'. -/
theorem fderiv_quaternionAction_pair (m : ℕ) (p dp : BinaryForm (m+1)) (v : ℍ) :
    fderiv ℝ (fun z : ℍ × BinaryForm (m+1) => polynomialRepresentation (m+1) (quaternionMatrix z.1) z.2)
      (1,p) (v,dp) = infinitesimalAction m (quaternionMatrix v) p + dp := by
  let A := fun z : ℍ × BinaryForm (m+1) => polynomialRepresentation (m+1) (quaternionMatrix z.1) z.2
  have hA : DifferentiableAt ℝ A (1,p) :=
    (contDiff_quaternionPolynomialRepresentation (m+1)).differentiable (by simp) (1,p)
  have hx : HasDerivAt (fun t : ℝ => 1 + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (1 : ℍ)
  have hp : HasDerivAt (fun t : ℝ => p + t • dp) dp 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const dp).const_add p
  have h1 : fderiv ℝ A (1,p) (v,0) = infinitesimalAction m (quaternionMatrix v) p := by
    have hd : HasFDerivAt A (fderiv ℝ A (1,p)) ((fun t : ℝ => (1+t • v,p)) 0) := by
      simpa using hA.hasFDerivAt
    have hc := hd.comp_hasDerivAt 0 (hx.prodMk (hasDerivAt_const (0:ℝ) p))
    exact hc.unique (by simpa only [A, Function.comp_def] using!
      quaternionPolynomialRepresentation_hasDerivAt m v p)
  have h2 : fderiv ℝ A (1,p) (0,dp) = dp := by
    have hd : HasFDerivAt A (fderiv ℝ A (1,p)) ((fun t : ℝ => ((1:ℍ),p+t • dp)) 0) := by
      simpa using hA.hasFDerivAt
    have hc := hd.comp_hasDerivAt 0 ((hasDerivAt_const (0:ℝ) (1:ℍ)).prodMk hp)
    exact hc.unique (by simpa [A, Function.comp_def] using hp)
  change fderiv ℝ A (1,p) (v,dp) = _
  rw [show (v,dp) = (v,0) + (0,dp) by simp, map_add, h1, h2]

end MathResearch.Spinor
