module
public import MathResearch.Spinor.SmoothCorrespondence

/-! Group laws and the automorphy cocycle on the actual quaternionic ball. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion Matrix.Norms.Elementwise
namespace MathResearch.Spinor

/-- Sp(1,1), bundled using the already verified two-sided matrix inverse equations. -/
def Sp11 := {g : QuaternionMatrix2 // IsSp11 g}

instance : Coe Sp11 QuaternionMatrix2 := ⟨Subtype.val⟩

instance : Group Sp11 where
  mul g h := ⟨g.val*h.val,g.property.mul h.property⟩
  one := ⟨1,by simp [IsSp11]⟩
  inv g := ⟨signatureAdjoint g.val,isSp11_signatureAdjoint g.property⟩
  mul_assoc a b c := Subtype.ext (mul_assoc a.val b.val c.val)
  one_mul a := Subtype.ext (one_mul a.val)
  mul_one a := Subtype.ext (mul_one a.val)
  inv_mul_cancel a := Subtype.ext a.property.1

@[simp] theorem Sp11.coe_mul (g h : Sp11) : (↑(g*h) : QuaternionMatrix2) = (g:QuaternionMatrix2)*h := rfl
@[simp] theorem Sp11.coe_one : (↑(1:Sp11) : QuaternionMatrix2)=1 := rfl
@[simp] theorem Sp11.coe_inv (g : Sp11) : (↑g⁻¹ : QuaternionMatrix2)=signatureAdjoint g := rfl

theorem Sp11.isSp11 (g : Sp11) : IsSp11 (g : QuaternionMatrix2) := g.property

/-- The cocycle keeps the noncommutative multiplication order. -/
theorem mobiusDenominator_cocycle (a b : QuaternionMatrix2) {q : ℍ}
    (hb : mobiusDenominator b q ≠ 0) :
    mobiusDenominator (a*b) q = mobiusDenominator a (mobiusPoint b q)*mobiusDenominator b q := by
  change b 1 0*q+b 1 1 ≠ 0 at hb
  simp only [mobiusDenominator, mobiusPoint, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [add_mul, mul_assoc, inv_mul_cancel₀ hb, mul_one]
  noncomm_ring

theorem mobiusPoint_mul (a b : QuaternionMatrix2) {q : ℍ}
    (hb : mobiusDenominator b q ≠ 0) : mobiusPoint (a*b) q = mobiusPoint a (mobiusPoint b q) := by
  have hn : (a*b) 0 0*q+(a*b) 0 1 =
      (a 0 0*mobiusPoint b q+a 0 1)*mobiusDenominator b q := by
    change b 1 0*q+b 1 1 ≠ 0 at hb
    simp only [mobiusPoint, mobiusDenominator, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [add_mul, mul_assoc, inv_mul_cancel₀ hb, mul_one]
    noncomm_ring
  unfold mobiusPoint at ⊢
  rw [hn, mobiusDenominator_cocycle a b hb, mul_inv_rev]
  simp only [mul_assoc, mul_inv_cancel_left₀ hb]
  rfl

@[simp] theorem mobiusDenominator_one (q : ℍ) : mobiusDenominator 1 q=1 := by simp [mobiusDenominator]
@[simp] theorem mobiusPoint_one (q : ℍ) : mobiusPoint 1 q=q := by simp [mobiusPoint]

/-- The concrete ball action as a genuine group action. -/
instance : MulAction Sp11 Ball where
  smul g q := ⟨mobiusPoint g q,mobiusPoint_mem_ball g.isSp11 q.property⟩
  one_smul q := Subtype.ext (mobiusPoint_one q)
  mul_smul g h q := Subtype.ext (mobiusPoint_mul g h (mobiusDenominator_ne_zero h.isSp11 q.property))

@[simp] theorem Sp11.smul_val (g : Sp11) (q : Ball) : (g • q).val = mobiusPoint g q := rfl

/-- The ball defining function transforms by the squared denominator norm. -/
theorem ballScale_mobius {g : QuaternionMatrix2} (hg : IsSp11 g) {q : ℍ} (hq : q ∈ Ball) :
    ballScale (mobiusPoint g q)=ballScale q / Quaternion.normSq (mobiusDenominator g q) := by
  rw [← groupOrigin_section_product g q hq, groupOrigin_scale (hg.mul (ballSection_isSp11 q hq)), section_product_entry]
  simp only [Quaternion.normSq_smul, inv_pow, mul_inv_rev, inv_inv]
  rw [Real.sq_sqrt hq.le]
  simp only [mobiusDenominator, div_eq_mul_inv, mul_comm]

/-- C7 is an action; composition reverses for the matrices supplied directly to ballAction. -/
theorem ballAction_mul (n : ℕ) (f : ℍ → BinaryForm n) {a b : QuaternionMatrix2}
    (ha : IsSp11 a) (hb : IsSp11 b) {q : ℍ} (hq : q ∈ Ball) :
    ballAction n (a*b) f q=ballAction n b (ballAction n a f) q := by
  have h₁ := fullLift_section_translate n (a*b) f q hq
  have h₂ := fullLift_section_translate n b (ballAction n a f) q hq
  rw [fullLift_ballAction n f ha (hb.mul (ballSection_isSp11 q hq)), ← mul_assoc] at h₂
  have he : weightedSpinor n (ballAction n (a*b) f) q=weightedSpinor n (ballAction n b (ballAction n a f)) q := h₁.symm.trans h₂
  exact (smul_right_injective _ (ne_of_gt (ballWeight_pos _ hq))) he

theorem ballRepresentation_mul (n : ℕ) (f : ℍ → BinaryForm n) {a b : QuaternionMatrix2}
    (ha : IsSp11 a) (hb : IsSp11 b) {q : ℍ} (hq : q ∈ Ball) :
    ballRepresentation n (a*b) f q=ballRepresentation n a (ballRepresentation n b f) q := by
  simp only [ballRepresentation, signatureAdjoint_mul]
  exact ballAction_mul n f (isSp11_signatureAdjoint hb) (isSp11_signatureAdjoint ha) hq

@[simp] theorem ballRepresentation_one (n : ℕ) (f : ℍ → BinaryForm n) (q : ℍ) :
    ballRepresentation n 1 f q=f q := by simp [ballRepresentation,ballAction]

end MathResearch.Spinor
