module
public import MathResearch.Spinor.ClassicalWeak
public import MathResearch.Spinor.L2StrongContinuity
public import MathResearch.Spinor.SmoothCorrespondence

/-! The actual regular kernel is invariant. Restricting the ambient unitary
representation therefore gives a strongly continuous regular representation. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion ContDiff
open MeasureTheory
namespace MathResearch.Spinor

theorem contDiffAt_ballAction (n : ℕ) {F : ℍ → BinaryForm n} {a : QuaternionMatrix2}
    (ha : IsSp11 a) {q : ℍ} (hq : q ∈ Ball) (hF : ContDiffAt ℝ ∞ F (mobiusPoint a q)) :
    ContDiffAt ℝ ∞ (ballAction n a F) q := by
  have hJ : ContDiffAt ℝ ∞ (mobiusDenominator a) q :=
    (contDiffAt_const.mul contDiffAt_id).add contDiffAt_const
  have hi := (contDiffAt_quaternionInv (mobiusDenominator_ne_zero ha hq)).comp q hJ
  have hp : ContDiffAt ℝ ∞ (mobiusPoint a) q :=
    ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const).mul hi
  have hs := (contDiff_normSq.contDiffAt.comp q hJ).inv
    (Quaternion.normSq_ne_zero.mpr (mobiusDenominator_ne_zero ha hq))
  have hpair := hi.prodMk (hF.comp q hp)
  have hpol : ContDiffAt ℝ ∞ (fun x : ℍ =>
      polynomialRepresentation n (quaternionMatrix ((mobiusDenominator a x)⁻¹)) (F (mobiusPoint a x))) q := by
    simpa only [Function.comp_def] using!
      (contDiff_quaternionPolynomialRepresentation n).contDiffAt.comp q hpair
  exact hs.smul hpol

theorem contDiffOn_ballRepresentation (n : ℕ) {F : ℍ → BinaryForm n}
    (hF : ContDiffOn ℝ ∞ F Ball) (g : Sp11) :
    ContDiffOn ℝ ∞ (ballRepresentation n g F) Ball := by
  intro q hq
  exact (contDiffAt_ballAction n (isSp11_signatureAdjoint g.property) hq
    ((hF _ (mobiusPoint_mem_ball (isSp11_signatureAdjoint g.property) hq)).contDiffAt
      (ball_isOpen.mem_nhds (mobiusPoint_mem_ball (isSp11_signatureAdjoint g.property) hq)))).contDiffWithinAt

/-- Invariance follows the written route: pass to the smooth representative,
apply the already checked lift/Schmid covariance, and return to weak L² classes. -/
theorem weightedL2Action_mem_weakKernel (n : ℕ) (hn : 2 ≤ n) (g : Sp11)
    (f : WeakBallSpace n hn) : weightedL2Action n hn g f.val ∈ weakKernel n hn := by
  obtain ⟨F, hF, hD, he⟩ := weakKernel_classicalRepresentative n hn f
  apply (mem_weakKernel_iff_classicalFueter n hn _ (contDiffOn_ballRepresentation n hF g)
    (weightedL2Action_ae_of_representative n hn g f.val F he)).mpr
  exact SC3_representation_covariance_v1 n (by omega) F
    (fun q hq => ((hF q hq).contDiffAt (ball_isOpen.mem_nhds hq)).differentiableAt (by simp))
    hD g.property

/-- The concrete unitary action restricted to actual Fueter-regular vectors. -/
def regularUnitary (n : ℕ) (hn : 2 ≤ n) (g : Sp11) :
    WeakBallSpace n hn ≃ₗᵢ[ℂ] WeakBallSpace n hn where
  toFun f := ⟨weightedL2Action n hn g f.val, weightedL2Action_mem_weakKernel n hn g f⟩
  invFun f := ⟨weightedL2Action n hn g⁻¹ f.val, weightedL2Action_mem_weakKernel n hn g⁻¹ f⟩
  map_add' f h := Subtype.ext (weightedL2Action_add n hn g f.val h.val)
  map_smul' c f := Subtype.ext (weightedL2Action_smul n hn g c f.val)
  left_inv f := by
    apply Subtype.ext
    change weightedL2Action n hn g⁻¹ (weightedL2Action n hn g f.val) = f.val
    rw [← weightedL2Action_mul, inv_mul_cancel, weightedL2Action_one]
  right_inv f := by
    apply Subtype.ext
    change weightedL2Action n hn g (weightedL2Action n hn g⁻¹ f.val) = f.val
    rw [← weightedL2Action_mul, mul_inv_cancel, weightedL2Action_one]
  norm_map' f := weightedL2Action_norm n hn g f.val

def regularRepresentation (n : ℕ) (hn : 2 ≤ n) :
    Sp11 →* (WeakBallSpace n hn ≃ₗᵢ[ℂ] WeakBallSpace n hn) where
  toFun := regularUnitary n hn
  map_one' := by
    ext f : 1
    exact Subtype.ext (weightedL2Action_one n hn f.val)
  map_mul' g h := by
    ext f : 1
    exact Subtype.ext (weightedL2Action_mul n hn g h f.val)

theorem stronglyContinuous_regularRepresentation (n : ℕ) (hn : 2 ≤ n)
    (f : WeakBallSpace n hn) : Continuous (fun g : Sp11 => regularRepresentation n hn g f) := by
  apply Continuous.subtype_mk
  exact stronglyContinuous_weightedL2Representation n hn f.val

end MathResearch.Spinor
