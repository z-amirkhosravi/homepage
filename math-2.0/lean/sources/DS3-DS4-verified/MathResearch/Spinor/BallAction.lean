module
public import MathResearch.Spinor.FullLift

/-! The explicit polynomial-spinor Möbius action preserves the Fueter kernel. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion BigOperators Matrix.Norms.Elementwise Topology
namespace MathResearch.Spinor

/-- The denominator cq+d, for the matrix actually acting on the ball. -/
def mobiusDenominator (a : QuaternionMatrix2) (q : ℍ) : ℍ := a 1 0*q+a 1 1

def mobiusPoint (a : QuaternionMatrix2) (q : ℍ) : ℍ :=
  (a 0 0*q+a 0 1)*(mobiusDenominator a q)⁻¹

/-- C7 with the inverse element supplied as a. `ballRepresentation` below inserts γ⁻¹. -/
def ballAction (n : ℕ) (a : QuaternionMatrix2) (f : ℍ → BinaryForm n) (q : ℍ) : BinaryForm n :=
  (Quaternion.normSq (mobiusDenominator a q))⁻¹ •
    polynomialRepresentation n (quaternionMatrix ((mobiusDenominator a q)⁻¹)) (f (mobiusPoint a q))

def ballRepresentation (n : ℕ) (γ : QuaternionMatrix2) (f : ℍ → BinaryForm n) : ℍ → BinaryForm n :=
  ballAction n (signatureAdjoint γ) f

theorem section_product_entry (a : QuaternionMatrix2) (q : ℍ) (i : Fin 2) :
    (a*ballSection q) i 1 = (Real.sqrt (ballScale q))⁻¹ • (a i 0*q+a i 1) := by
  simp [ballSection, Matrix.mul_apply, Fin.sum_univ_two, smul_add]

theorem inverse_real_smul (r : ℝ) (q : ℍ) : (r • q)⁻¹ = r⁻¹ • q⁻¹ := by
  simp only [Algebra.smul_def, mul_inv_rev]
  change q⁻¹ * (r:ℍ)⁻¹ = (r⁻¹:ℝ) * q⁻¹
  rw [← Quaternion.coe_inv, Quaternion.coe_commutes]

theorem groupOrigin_section_product (a : QuaternionMatrix2) (q : ℍ) (hq : q ∈ Ball) :
    groupOrigin (a*ballSection q) = mobiusPoint a q := by
  have hs := (Real.sqrt_pos.mpr hq).ne'
  simp only [groupOrigin, section_product_entry, inverse_real_smul, inv_inv,
    smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hs, one_smul]
  rfl

theorem mobiusDenominator_ne_zero {a : QuaternionMatrix2} (ha : IsSp11 a) {q : ℍ} (hq : q ∈ Ball) :
    mobiusDenominator a q ≠ 0 := by
  have h := (ha.mul (ballSection_isSp11 q hq)).lowerRight_ne_zero
  rw [section_product_entry] at h
  intro hz
  exact h (by change (Real.sqrt (ballScale q))⁻¹ • mobiusDenominator a q = 0; rw [hz, smul_zero])

theorem mobiusPoint_mem_ball {a : QuaternionMatrix2} (ha : IsSp11 a) {q : ℍ} (hq : q ∈ Ball) :
    mobiusPoint a q ∈ Ball := by
  rw [← groupOrigin_section_product a q hq]
  exact groupOrigin_mem_ball (ha.mul (ballSection_isSp11 q hq))

theorem sqrt_pow_scale (n : ℕ) {s : ℝ} (hs : 0 < s) : s * Real.sqrt s ^ n = s ^ (((n:ℝ)+2)/2) := by
  calc
    _ = s^((1:ℝ)) * s^((1/2:ℝ)*(n:ℝ)) := by rw [Real.rpow_one, Real.rpow_mul_natCast hs.le, ← Real.sqrt_eq_rpow]
    _ = _ := by rw [← Real.rpow_add hs]; congr 1; ring

/-- Left translation of L2 gives precisely the explicit ball formula C7. -/
theorem fullLift_section_translate (n : ℕ) (a : QuaternionMatrix2) (f : ℍ → BinaryForm n)
    (q : ℍ) (hq : q ∈ Ball) :
    fullLift n f (a*ballSection q) = weightedSpinor n (ballAction n a f) q := by
  simp only [fullLift, section_product_entry, groupOrigin_section_product a q hq,
    Quaternion.normSq_smul, inverse_real_smul, inv_inv, quaternionAction_real_smul,
    mul_inv_rev, inv_pow, inv_inv, smul_smul]
  rw [Real.sq_sqrt hq.le]
  simp only [weightedSpinor, ballAction, ballWeight, smul_smul]
  congr 1
  rw [← sqrt_pow_scale n hq]
  unfold mobiusDenominator
  ring

/-- Removing the positive scalar section weight. -/
def unweightedSpinor (n : ℕ) (U : ℍ → BinaryForm n) (q : ℍ) : BinaryForm n :=
  ballWeight (-((n:ℝ)+2)/2) q • U q

theorem weight_unweight (n : ℕ) (U : ℍ → BinaryForm n) {q : ℍ} (hq : q ∈ Ball) :
    weightedSpinor n (unweightedSpinor n U) q = U q := by
  simp only [weightedSpinor, unweightedSpinor, ballWeight, smul_smul]
  rw [← Real.rpow_add hq, show ((n:ℝ)+2)/2+(-((n:ℝ)+2)/2)=0 by ring, Real.rpow_zero, one_smul]

theorem unweight_weight (n : ℕ) (f : ℍ → BinaryForm n) {q : ℍ} (hq : q ∈ Ball) :
    unweightedSpinor n (weightedSpinor n f) q = f q := by
  simp only [weightedSpinor, unweightedSpinor, ballWeight, smul_smul]
  rw [← Real.rpow_add hq, show (-((n:ℝ)+2)/2)+((n:ℝ)+2)/2=0 by ring, Real.rpow_zero, one_smul]

/-- L2 and restriction to the section with the inverse weight are inverse on G. -/
theorem fullLift_recover (n : ℕ) (F : QuaternionMatrix2 → BinaryForm n)
    (hF : RightEquivariant n F) {g : QuaternionMatrix2} (hg : IsSp11 g) :
    fullLift n (unweightedSpinor n (fun q => F (ballSection q))) g = F g := by
  rw [← frameLift_weighted_eq_fullLift n _ hg]
  unfold frameLift
  rw [weight_unweight n _ (groupOrigin_mem_ball hg)]
  exact frameLift_recover n F hF hg

theorem fullLift_rightEquivariant (n : ℕ) (f : ℍ → BinaryForm n) : RightEquivariant n (fullLift n f) := by
  intro g hg a b ha hb
  rw [← frameLift_weighted_eq_fullLift n f (hg.mul (compactMatrix_isSp11 a b ha hb)),
    ← frameLift_weighted_eq_fullLift n f hg, frameLift_equivariant n _ g a b]
  intro h; simp [h] at hb

theorem rightEquivariant_left_translate (n : ℕ) (F : QuaternionMatrix2 → BinaryForm n)
    (hF : RightEquivariant n F) {a : QuaternionMatrix2} (ha : IsSp11 a) :
    RightEquivariant n (fun g => F (a*g)) := by
  intro g hg kL kR hL hR
  simpa only [← mul_assoc] using hF (a*g) (ha.mul hg) kL kR hL hR

/-- L2 intertwines the explicit ball action and left translation, on all of G. -/
theorem fullLift_ballAction (n : ℕ) (f : ℍ → BinaryForm n) {a : QuaternionMatrix2} (ha : IsSp11 a)
    {g : QuaternionMatrix2} (hg : IsSp11 g) : fullLift n (ballAction n a f) g = fullLift n f (a*g) := by
  have hK := rightEquivariant_left_translate n (fullLift n f) (fullLift_rightEquivariant n f) ha
  rw [← frameLift_weighted_eq_fullLift n _ hg]
  have he : frameLift n (weightedSpinor n (ballAction n a f)) g =
      frameLift n (fun q => fullLift n f (a*ballSection q)) g := by
    unfold frameLift
    exact congrArg _ (fullLift_section_translate n a f _ (groupOrigin_mem_ball hg)).symm
  rw [he]
  exact frameLift_recover n _ hK hg

theorem differentiableAt_ballAction (n : ℕ) (f : ℍ → BinaryForm n) {a : QuaternionMatrix2}
    (ha : IsSp11 a) {q : ℍ} (hq : q ∈ Ball) (hf : DifferentiableAt ℝ f (mobiusPoint a q)) :
    DifferentiableAt ℝ (ballAction n a f) q := by
  have hJ : DifferentiableAt ℝ (mobiusDenominator a) q :=
    (differentiableAt_id.const_mul (a 1 0)).add_const (a 1 1)
  have hi := (hasFDerivAt_inv' (mobiusDenominator_ne_zero ha hq)).differentiableAt.comp q hJ
  have hpoint : DifferentiableAt ℝ (mobiusPoint a) q :=
    ((differentiableAt_id.const_mul (a 0 0)).add_const (a 0 1)).mul hi
  have hs := (hasFDerivAt_inv (Quaternion.normSq_ne_zero.mpr (mobiusDenominator_ne_zero ha hq))).differentiableAt.comp q
    ((differentiableAt_normSq _).comp q hJ)
  have hp := hi.prodMk (hf.comp q hpoint)
  have hr : DifferentiableAt ℝ (fun x : ℍ => polynomialRepresentation n (quaternionMatrix ((mobiusDenominator a x)⁻¹)) (f (mobiusPoint a x))) q := by
    simpa only [Function.comp_def] using!
      (((contDiff_quaternionPolynomialRepresentation n).differentiable (by simp)
        ((mobiusDenominator a q)⁻¹, f (mobiusPoint a q))).comp q hp)
  exact hs.smul hr

/-- SC3's covariance conclusion, for every coefficient and every degree n≥1. -/
theorem SC3_ball_covariance_v1 (n : ℕ) (hn : 1 ≤ n) (f : ℍ → BinaryForm n)
    (hf : ∀ q ∈ Ball, DifferentiableAt ℝ f q)
    (hkernel : ∀ q ∈ Ball, ∀ d, Fueter.leftOperator (fun x => fueterCoefficientCLM n d (f x)) q = 0)
    {a : QuaternionMatrix2} (ha : IsSp11 a) :
    ∀ q ∈ Ball, ∀ d, Fueter.leftOperator (fun x => fueterCoefficientCLM n d (ballAction n a f x)) q = 0 := by
  have hb : ∀ q ∈ Ball, DifferentiableAt ℝ (ballAction n a f) q := fun q hq =>
    differentiableAt_ballAction n f ha hq (hf _ (mobiusPoint_mem_ball ha hq))
  apply (SC3_v1 n hn (ballAction n a f) hb).2.mp
  have hG := (SC3_v1 n hn f hf).2.mpr hkernel
  intro g hg d
  have hnew := differentiableAt_fullLift n (ballAction n a f) hg (hb _ (groupOrigin_mem_ball hg))
  have hold := (differentiableAt_fullLift n f (ha.mul hg) (hf _ (groupOrigin_mem_ball (ha.mul hg)))).comp g
    (matrixLeftCLM a).differentiableAt
  rw [schmidOperator, projectedGroupOperator_congr_on_group n _ (fun x => fullLift n f (a*x))
    (fun x hx => fullLift_ballAction n f ha hx) hg hnew hold,
    projectedGroupOperator_left_translate]
  exact hG (a*g) (ha.mul hg) d

/-- The standard inverse-element convention of C7 preserves the kernel. -/
theorem SC3_representation_covariance_v1 (n : ℕ) (hn : 1 ≤ n) (f : ℍ → BinaryForm n)
    (hf : ∀ q ∈ Ball, DifferentiableAt ℝ f q)
    (hkernel : ∀ q ∈ Ball, ∀ d, Fueter.leftOperator (fun x => fueterCoefficientCLM n d (f x)) q = 0)
    {γ : QuaternionMatrix2} (hγ : IsSp11 γ) :
    ∀ q ∈ Ball, ∀ d, Fueter.leftOperator (fun x => fueterCoefficientCLM n d (ballRepresentation n γ f x)) q = 0 :=
  SC3_ball_covariance_v1 n hn f hf hkernel (isSp11_signatureAdjoint hγ)

end MathResearch.Spinor
