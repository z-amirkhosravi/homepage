module
public import MathResearch.Spinor.GroupKernel

/-! The explicit L2 lift, section weights, and the ball action. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion BigOperators Matrix.Norms.Elementwise
open MvPolynomial
namespace MathResearch.Spinor

theorem monomialForm_eq (n : ℕ) (k : Fin (n+1)) :
    (monomialForm n k : ComplexPoly2) = X 0 ^ (n-k.val) * X 1 ^ k.val := by
  simp [monomialForm, exponent, X_pow_eq_monomial ]

theorem polynomialRepresentation_scalar (n : ℕ) (r : ℝ) (p : BinaryForm n) :
    polynomialRepresentation n (quaternionMatrix (r : ℍ)) p = r^n • p := by
  have hm (k : Fin (n+1)) :
      polynomialRepresentation n (quaternionMatrix (r : ℍ)) (monomialForm n k) = r^n • monomialForm n k := by
    apply Subtype.ext
    change polynomialAction (quaternionMatrix (r : ℍ)) (monomialForm n k) = (r^n : ℝ) • (monomialForm n k : ComplexPoly2)
    rw [monomialForm_eq]
    simp only [map_mul, map_pow, polynomialAction_X]
    have h0 : substitution (quaternionMatrix (r : ℍ)) 0 = C (r:ℂ) * X 0 := by simp [substitution, quaternionMatrix]
    have h1 : substitution (quaternionMatrix (r : ℍ)) 1 = C (r:ℂ) * X 1 := by simp [substitution, quaternionMatrix]
    rw [h0, h1, mul_pow, mul_pow]
    rw [← IsScalarTower.algebraMap_smul ℂ (r^n), smul_eq_C_mul]
    change _ = C ((r^n:ℝ):ℂ) * _
    rw [Complex.ofReal_pow]
    have he : (C (r:ℂ) : ComplexPoly2)^(n-k.val) * (C (r:ℂ))^k.val = C ((r:ℂ)^n) := by
      rw [← pow_add, Nat.sub_add_cancel (by omega), map_pow]
    rw [← he]
    ring
  conv_lhs => rw [← monomialForm_expansion n p]
  simp only [map_sum, map_smul, hm]
  calc
    _ = r^n • (∑ k, coefficients n p k • monomialForm n k) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro k _
      exact smul_comm _ _ _
    _ = _ := by rw [monomialForm_expansion]

theorem quaternionAction_real_smul (n : ℕ) (r : ℝ) (a : ℍ) (p : BinaryForm n) :
    polynomialRepresentation n (quaternionMatrix (r • a)) p = r^n • polynomialRepresentation n (quaternionMatrix a) p := by
  rw [show r • a = (r:ℍ)*a by rw [Algebra.smul_def]; rfl, quaternionMatrix_mul, map_mul]
  exact polynomialRepresentation_scalar n r _

/-- The exact lift (L2), since normSq d = |d|². -/
def fullLift (n : ℕ) (f : ℍ → BinaryForm n) (g : QuaternionMatrix2) : BinaryForm n :=
  (Quaternion.normSq (g 1 1))⁻¹ • polynomialRepresentation n (quaternionMatrix ((g 1 1)⁻¹)) (f (groupOrigin g))

theorem sqrt_weight_cancel (n : ℕ) {s : ℝ} (hs : 0 < s) :
    (Real.sqrt s)⁻¹ ^ n * s ^ (((n:ℝ)+2)/2) = s := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hs.le, ← Real.rpow_mul_natCast hs.le, ← Real.rpow_add hs]
  rw [show -(1/2:ℝ)*(n:ℝ)+((n:ℝ)+2)/2=1 by ring, Real.rpow_one]

/-- The canonical frame lift is precisely the wiki's explicit lift on every point of G. -/
theorem frameLift_weighted_eq_fullLift (n : ℕ) (f : ℍ → BinaryForm n)
    {g : QuaternionMatrix2} (hg : IsSp11 g) : frameLift n (weightedSpinor n f) g = fullLift n f g := by
  have hi : (compactRight g)⁻¹ = (Real.sqrt (ballScale (groupOrigin g)))⁻¹ • (g 1 1)⁻¹ := by
    simp only [compactRight, Algebra.smul_def, mul_inv_rev]
    change (g 1 1)⁻¹ * (Real.sqrt (ballScale (groupOrigin g)) : ℍ)⁻¹ =
      ((Real.sqrt (ballScale (groupOrigin g)))⁻¹ : ℝ) * (g 1 1)⁻¹
    rw [← Quaternion.coe_inv, Quaternion.coe_commutes]
  simp only [frameLift, hi, quaternionAction_real_smul, weightedSpinor]
  rw [LinearMap.map_smul_of_tower, smul_smul]
  rw [ballWeight, sqrt_weight_cancel n (groupOrigin_mem_ball hg), groupOrigin_scale hg]
  rfl

/-- The section value of L2 is exactly L3. -/
theorem fullLift_section (n : ℕ) (f : ℍ → BinaryForm n) (q : ℍ) (hq : q ∈ Ball) :
    fullLift n f (ballSection q) = weightedSpinor n f q := by
  rw [← frameLift_weighted_eq_fullLift n f (ballSection_isSp11 q hq), frameLift_section n _ q hq]

theorem differentiableAt_normSq (q : ℍ) : DifferentiableAt ℝ Quaternion.normSq q := by
  simpa only [id_eq, Quaternion.inner_self] using! (differentiableAt_id.inner ℝ differentiableAt_id :
    DifferentiableAt ℝ (fun x : ℍ => inner ℝ x x) q)

theorem differentiableAt_fullLift (n : ℕ) (f : ℍ → BinaryForm n) {g : QuaternionMatrix2}
    (hg : IsSp11 g) (hf : DifferentiableAt ℝ f (groupOrigin g)) : DifferentiableAt ℝ (fullLift n f) g := by
  have hd := (entryCLM 1 1).differentiableAt (x := g)
  have hs := (hasFDerivAt_inv (Quaternion.normSq_ne_zero.mpr hg.lowerRight_ne_zero)).differentiableAt.comp g
    ((differentiableAt_normSq (g 1 1)).comp g hd)
  have hi := (hasFDerivAt_inv' hg.lowerRight_ne_zero).differentiableAt.comp g hd
  have hp := hi.prodMk (hf.comp g (differentiableAt_groupOrigin hg.lowerRight_ne_zero))
  have hr : DifferentiableAt ℝ (fun z : QuaternionMatrix2 => polynomialRepresentation n (quaternionMatrix ((z 1 1)⁻¹)) (f (groupOrigin z))) g := by
    simpa only [Function.comp_def, entryCLM_apply] using!
      (((contDiff_quaternionPolynomialRepresentation n).differentiable (by simp)
        ((g 1 1)⁻¹, f (groupOrigin g))).comp g hp)
  exact hs.smul hr

theorem differentiableAt_weightedSpinor (n : ℕ) (f : ℍ → BinaryForm n) {q : ℍ}
    (hq : q ∈ Ball) (hf : DifferentiableAt ℝ f q) : DifferentiableAt ℝ (weightedSpinor n f) q :=
  ((hasFDerivAt_ballWeight _ hq).smul hf.hasFDerivAt).differentiableAt

/-- The verified SC3 statement for the exact L2 lift, rather than just its frame formula. -/
theorem SC3_v1 (n : ℕ) (hn : 1 ≤ n) (f : ℍ → BinaryForm n)
    (hf : ∀ q ∈ Ball, DifferentiableAt ℝ f q) :
    (∀ q ∈ Ball, ∀ d, (24 : ℝ) • schmidOperator n (fullLift n f) (ballSection q) d =
      ballWeight (((n:ℝ)+4)/2) q • Fueter.leftOperator (fun x => fueterCoefficientCLM n d (f x)) q) ∧
    ((∀ g, IsSp11 g → ∀ d, schmidOperator n (fullLift n f) g d = 0) ↔
      (∀ q ∈ Ball, ∀ d, Fueter.leftOperator (fun x => fueterCoefficientCLM n d (f x)) q = 0)) := by
  have he (g : QuaternionMatrix2) (hg : IsSp11 g) (d : Fin 2 →₀ ℕ) :
      schmidOperator n (frameLift n (weightedSpinor n f)) g d = schmidOperator n (fullLift n f) g d := by
    rw [schmidOperator, schmidOperator,
      projectedGroupOperator_congr_on_group n _ _ (fun g hg => frameLift_weighted_eq_fullLift n f hg) hg
        (differentiableAt_frameLift n _ hg (differentiableAt_weightedSpinor n f (groupOrigin_mem_ball hg)
          (hf _ (groupOrigin_mem_ball hg)))) (differentiableAt_fullLift n f hg (hf _ (groupOrigin_mem_ball hg)))]
  have h := SC3_frameLift_v1 n hn f hf
  constructor
  · intro q hq d
    rw [← he _ (ballSection_isSp11 q hq) d]
    exact h.1 q hq d
  · rw [← h.2]
    apply forall_congr'; intro g
    apply forall_congr'; intro hg
    simp only [he g hg]

end MathResearch.Spinor
