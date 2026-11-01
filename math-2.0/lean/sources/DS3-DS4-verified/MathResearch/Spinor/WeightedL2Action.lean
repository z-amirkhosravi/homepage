module
public import MathResearch.Spinor.MobiusMeasure
public import MathResearch.Spinor.CoefficientEmbedding

/-! Descent of DS2's formula C7 to the actual weighted L² space.
Integrability is proved by the written Jacobian/weight cancellation, separately
from the equality of total integrals. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion ENNReal
open MeasureTheory
namespace MathResearch.Spinor

theorem integrable_weighted_iff (n : ℕ) (hn : 2 ≤ n) (f : ℍ → ℝ) :
    Integrable f (weightedBallMeasure n) ↔ IntegrableOn (fun q => ballDensity n q * f q) Ball := by
  rw [weightedBallMeasure, integrable_withDensity_iff_integrable_smul'
    (continuous_ballDensity n).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem ball_isOpen.measurableSet] with q hq
  rw [ENNReal.toReal_ofReal (ballDensity_pos n hn hq).le, smul_eq_mul]

/-- C7 preserves actual square-integrability, by Jacobian change of variables. -/
theorem ballAction_memLp (n : ℕ) (hn : 2 ≤ n) {g : QuaternionMatrix2} (hg : IsSp11 g)
    {f : ℍ → BinaryForm n} (hf : MemLp f 2 (weightedBallMeasure n)) :
    MemLp (ballAction n g f) 2 (weightedBallMeasure n) := by
  apply (memLp_two_iff_integrable_sq_norm (ballAction_aestronglyMeasurable n hn hg hf.aestronglyMeasurable)).mpr
  rw [integrable_weighted_iff n hn]
  have hi := (integrable_weighted_iff n hn (fun q => ‖f q‖^2)).mp
    ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf)
  have hcv := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (volume : Measure ℍ)
    ball_isOpen.measurableSet
    (fun q hq => (hasFDerivAt_mobiusPoint g (mobiusDenominator_ne_zero hg hq)).hasFDerivWithinAt)
    (mobiusPoint_bijOn hg).injOn (fun q => ballDensity n q * ‖f q‖^2)
  rw [(mobiusPoint_bijOn hg).image_eq] at hcv
  apply (hcv.mp hi).congr
  filter_upwards [ae_restrict_mem ball_isOpen.measurableSet] with q hq
  have hd : (mobiusDerivative g q).det = (Quaternion.normSq (mobiusDenominator g q))⁻¹ ^ 4 := by
    rw [← (hasFDerivAt_mobiusPoint g (mobiusDenominator_ne_zero hg hq)).fderiv]
    exact mobiusJacobian g hg q hq
  rw [hd, abs_of_nonneg (by positivity), smul_eq_mul, ← mul_assoc,
    weighted_density_cancellation n hn hg hq, ballAction_norm, mul_pow]
  ring

def weightedL2Action (n : ℕ) (hn : 2 ≤ n) (g : Sp11) (f : BallL2 n) : BallL2 n :=
  (ballAction_memLp n hn (isSp11_signatureAdjoint g.property) (Lp.memLp f)).toLp
    (ballRepresentation n g f)

theorem weightedL2Action_ae (n : ℕ) (hn : 2 ≤ n) (g : Sp11) (f : BallL2 n) :
    (weightedL2Action n hn g f : ℍ → BinaryForm n) =ᵐ[weightedBallMeasure n]
      ballRepresentation n g f := MemLp.coeFn_toLp _

theorem weightedL2Action_norm (n : ℕ) (hn : 2 ≤ n) (g : Sp11) (f : BallL2 n) :
    ‖weightedL2Action n hn g f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [ballL2_norm_sq_integral n hn, ballL2_norm_sq_integral n hn]
  calc
    _ = ∫ q in Ball, ballDensity n q * ‖ballRepresentation n g f q‖^2 := by
      apply integral_congr_ae
      exact ((ae_weightedBall_iff n hn _).mp (weightedL2Action_ae n hn g f)).mono
        (fun q hq => congrArg (fun p : BinaryForm n => ballDensity n q * ‖p‖^2) hq)
    _ = _ := weighted_integral_ballAction n hn f (isSp11_signatureAdjoint g.property)

theorem weightedL2Action_add (n : ℕ) (hn : 2 ≤ n) (g : Sp11) (f r : BallL2 n) :
    weightedL2Action n hn g (f+r) = weightedL2Action n hn g f + weightedL2Action n hn g r := by
  apply Lp.ext
  have ha := (mobius_quasiMeasurePreserving_weighted n hn
    (isSp11_signatureAdjoint g.property)).ae (Lp.coeFn_add f r)
  filter_upwards [weightedL2Action_ae n hn g (f+r), weightedL2Action_ae n hn g f,
    weightedL2Action_ae n hn g r, Lp.coeFn_add (weightedL2Action n hn g f)
      (weightedL2Action n hn g r), ha] with q h₁ h₂ h₃ h₄ h₅
  rw [h₁, h₄]
  simp only [Pi.add_apply] at h₅ ⊢
  rw [h₂, h₃]
  simp only [ballRepresentation, ballAction, h₅, map_add, smul_add]

theorem weightedL2Action_smul (n : ℕ) (hn : 2 ≤ n) (g : Sp11) (c : ℂ) (f : BallL2 n) :
    weightedL2Action n hn g (c • f) = c • weightedL2Action n hn g f := by
  apply Lp.ext
  have ha := (mobius_quasiMeasurePreserving_weighted n hn
    (isSp11_signatureAdjoint g.property)).ae (Lp.coeFn_smul c f)
  filter_upwards [weightedL2Action_ae n hn g (c • f), weightedL2Action_ae n hn g f,
    Lp.coeFn_smul c (weightedL2Action n hn g f), ha] with q h₁ h₂ h₃ h₄
  rw [h₁, h₃]
  simp only [Pi.smul_apply] at h₄ ⊢
  rw [h₂]
  simp only [ballRepresentation, ballAction, h₄, map_smul]
  exact smul_comm _ _ _

theorem weightedL2Action_one (n : ℕ) (hn : 2 ≤ n) (f : BallL2 n) :
    weightedL2Action n hn 1 f = f := by
  apply Lp.ext
  filter_upwards [weightedL2Action_ae n hn 1 f] with q hq
  simpa using hq

/-- The group-law argument specified in the written proof: use the denominator
cocycle directly, including the order of quaternionic inverse multiplication. -/
theorem ballAction_mul_by_cocycle (n : ℕ) (f : ℍ → BinaryForm n)
    {a b : QuaternionMatrix2} (hb : IsSp11 b) {q : ℍ} (hq : q ∈ Ball) :
    ballAction n (a*b) f q = ballAction n b (ballAction n a f) q := by
  have hJ := mobiusDenominator_ne_zero hb hq
  simp only [ballAction, mobiusPoint_mul a b hJ, mobiusDenominator_cocycle a b hJ,
    map_mul, mul_inv_rev, quaternionMatrix_mul, Module.End.mul_apply,
    LinearMap.map_smul_of_tower, smul_smul]

theorem ballRepresentation_mul_by_cocycle (n : ℕ) (f : ℍ → BinaryForm n)
    {a b : QuaternionMatrix2} (ha : IsSp11 a) {q : ℍ} (hq : q ∈ Ball) :
    ballRepresentation n (a*b) f q =
      ballRepresentation n a (ballRepresentation n b f) q := by
  simp only [ballRepresentation, signatureAdjoint_mul]
  exact ballAction_mul_by_cocycle n f (isSp11_signatureAdjoint ha) hq

theorem weightedL2Action_mul (n : ℕ) (hn : 2 ≤ n) (g h : Sp11) (f : BallL2 n) :
    weightedL2Action n hn (g*h) f = weightedL2Action n hn g (weightedL2Action n hn h f) := by
  apply Lp.ext
  have ha := (mobius_quasiMeasurePreserving_weighted n hn
    (isSp11_signatureAdjoint g.property)).ae (weightedL2Action_ae n hn h f)
  have hB : ∀ᵐ q ∂weightedBallMeasure n, q ∈ Ball :=
    (ae_weightedBall_iff n hn _).mpr (ae_restrict_mem ball_isOpen.measurableSet)
  filter_upwards [weightedL2Action_ae n hn (g*h) f,
    weightedL2Action_ae n hn g (weightedL2Action n hn h f), ha, hB] with q h₁ h₂ h₃ hq
  rw [h₁, h₂]
  change ballRepresentation n ((g : QuaternionMatrix2)*(h : QuaternionMatrix2)) f q = _
  rw [ballRepresentation_mul_by_cocycle n f g.property hq]
  simp only [ballRepresentation, ballAction] at h₃ ⊢
  rw [h₃]

/-- The concrete ambient C7 action, with norm preservation and inverse proved. -/
def weightedL2Unitary (n : ℕ) (hn : 2 ≤ n) (g : Sp11) : BallL2 n ≃ₗᵢ[ℂ] BallL2 n where
  toFun := weightedL2Action n hn g
  invFun := weightedL2Action n hn g⁻¹
  map_add' := weightedL2Action_add n hn g
  map_smul' := weightedL2Action_smul n hn g
  left_inv f := by rw [← weightedL2Action_mul, inv_mul_cancel, weightedL2Action_one]
  right_inv f := by rw [← weightedL2Action_mul, mul_inv_cancel, weightedL2Action_one]
  norm_map' := weightedL2Action_norm n hn g

def weightedL2Representation (n : ℕ) (hn : 2 ≤ n) :
    Sp11 →* (BallL2 n ≃ₗᵢ[ℂ] BallL2 n) where
  toFun := weightedL2Unitary n hn
  map_one' := by ext f : 1; exact weightedL2Action_one n hn f
  map_mul' g h := by ext f : 1; exact weightedL2Action_mul n hn g h f

end MathResearch.Spinor
