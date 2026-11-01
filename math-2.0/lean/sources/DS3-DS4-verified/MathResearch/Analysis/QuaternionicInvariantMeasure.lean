module
public import MathResearch.Analysis.QuaternionicHaarCoordinates
public import MathResearch.Spinor.MobiusMeasure

/-! The invariant measure (1-|q|²)⁻⁴ dq on the quaternionic ball.
This is the base measure in the separately proved quotient-Haar theorem. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Quaternion ENNReal
open MeasureTheory MeasureTheory.Measure
namespace MathResearch.Spinor

def invariantBallDensity (q : ℍ) : ℝ := (ballScale q)⁻¹ ^ 4

def invariantBallMeasure : Measure ℍ :=
  (volume.restrict Ball).withDensity (fun q => ENNReal.ofReal (invariantBallDensity q))

theorem measurable_invariantBallDensity : Measurable invariantBallDensity :=
  (contDiff_ballScale.continuous.measurable.inv).pow_const 4

theorem invariantBallDensity_pos {q : ℍ} (hq : q ∈ Ball) : 0 < invariantBallDensity q :=
  pow_pos (inv_pos.mpr hq) 4

/-- Cancellation of the density with the exact real four-dimensional Jacobian. -/
theorem invariantBallDensity_change {g : QuaternionMatrix2} (hg : IsSp11 g)
    {q : ℍ} (hq : q ∈ Ball) :
    mobiusJacobianDensity g q * ENNReal.ofReal (invariantBallDensity (mobiusPoint g q)) =
      ENNReal.ofReal (invariantBallDensity q) := by
  unfold mobiusJacobianDensity invariantBallDensity
  rw [← ENNReal.ofReal_mul (by positivity), ballScale_mobius hg hq]
  congr 1
  have hd : Quaternion.normSq (mobiusDenominator g q) ≠ 0 :=
    Quaternion.normSq_ne_zero.mpr (mobiusDenominator_ne_zero hg hq)
  field_simp

/-- Möbius transformations preserve the invariant ball measure. -/
theorem mobius_map_invariantBallMeasure {g : QuaternionMatrix2} (hg : IsSp11 g) :
    Measure.map (mobiusPoint g) invariantBallMeasure = invariantBallMeasure := by
  apply Measure.ext_of_lintegral
  intro f hf
  let w : ℍ → ℝ≥0∞ := fun q => ENNReal.ofReal (invariantBallDensity q)
  have hw : Measurable w := measurable_invariantBallDensity.ennreal_ofReal
  change (∫⁻ q, f q ∂Measure.map (mobiusPoint g) ((volume.restrict Ball).withDensity w)) =
    ∫⁻ q, f q ∂(volume.restrict Ball).withDensity w
  rw [lintegral_map hf (measurable_mobiusPoint g),
    lintegral_withDensity_eq_lintegral_mul _ hw (show Measurable (fun q => f (mobiusPoint g q)) from hf.comp (measurable_mobiusPoint g)),
    lintegral_withDensity_eq_lintegral_mul _ hw hf]
  simp only [Pi.mul_apply]
  calc
    _ = ∫⁻ q in Ball, mobiusJacobianDensity g q * (w (mobiusPoint g q) * f (mobiusPoint g q)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem ball_isOpen.measurableSet] with q hq
      rw [← mul_assoc, invariantBallDensity_change hg hq]
    _ = ∫⁻ q, (w q * f q) ∂Measure.map (mobiusPoint g)
        ((volume.restrict Ball).withDensity (mobiusJacobianDensity g)) := by
      rw [lintegral_map (show Measurable (fun q => w q * f q) from hw.mul hf) (measurable_mobiusPoint g),
        lintegral_withDensity_eq_lintegral_mul _ (measurable_mobiusJacobianDensity g)
          (show Measurable (fun q => w (mobiusPoint g q) * f (mobiusPoint g q)) from (hw.mul hf).comp (measurable_mobiusPoint g))]
      rfl
    _ = _ := by rw [mobius_map_jacobian hg]

/-- Lebesgue measure on the open-ball subtype. -/
def ballVolume : Measure Ball := volume.comap (Subtype.val : Ball → ℍ)

instance : IsFiniteMeasure ballVolume := by
  constructor
  rw [ballVolume, (MeasurableEmbedding.subtype_coe ball_isOpen.measurableSet).comap_apply]
  simpa only [Set.image_univ, Subtype.range_coe, show Ball = Metric.ball (0 : ℍ) 1 from Set.ext (fun q => by
    simpa only [Metric.mem_ball, dist_zero_right] using mem_ball_iff q)] using
    (Metric.isBounded_ball (x := (0 : ℍ)) (r := 1)).measure_lt_top (μ := volume)

instance : IsOpenPosMeasure ballVolume :=
  IsOpenPosMeasure.comap volume ball_isOpen.isOpenEmbedding_subtypeVal

/-- The invariant measure as a measure on the actual ball subtype. -/
def ballInvariantMeasure : Measure Ball :=
  ballVolume.withDensity (fun q => ENNReal.ofReal (invariantBallDensity q))

theorem continuous_invariantBallDensity_subtype :
    Continuous (fun q : Ball => invariantBallDensity q) := by
  exact ((contDiff_ballScale.continuous.comp continuous_subtype_val).inv₀
    (fun q => ne_of_gt q.property)).pow 4

instance : IsLocallyFiniteMeasure ballInvariantMeasure :=
  IsLocallyFiniteMeasure.withDensity_ofReal continuous_invariantBallDensity_subtype

instance : SigmaFinite ballInvariantMeasure := by
  unfold ballInvariantMeasure
  infer_instance

instance : IsOpenPosMeasure ballInvariantMeasure := by
  have ha : ballVolume ≪ ballInvariantMeasure :=
    withDensity_absolutelyContinuous'
      continuous_invariantBallDensity_subtype.measurable.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun q => ENNReal.ofReal_ne_zero_iff.mpr
        (invariantBallDensity_pos q.property))
  exact ⟨fun U hU hne hzero => (hU.measure_ne_zero ballVolume hne) (ha hzero)⟩

theorem map_ballInvariantMeasure :
    Measure.map (Subtype.val : Ball → ℍ) ballInvariantMeasure = invariantBallMeasure := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf measurable_subtype_coe]
  change (∫⁻ q : Ball, f q ∂ballVolume.withDensity
      (fun q => ENNReal.ofReal (invariantBallDensity q))) = _
  rw [lintegral_withDensity_eq_lintegral_mul _
    continuous_invariantBallDensity_subtype.measurable.ennreal_ofReal
    (show Measurable (fun q : Ball => f q) from hf.comp measurable_subtype_coe)]
  simp only [Pi.mul_apply]
  rw [ballVolume]
  rw [lintegral_subtype_comap ball_isOpen.measurableSet (fun q => ENNReal.ofReal (invariantBallDensity q) * f q)]
  unfold invariantBallMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _ measurable_invariantBallDensity.ennreal_ofReal hf]
  rfl

/-- The actual G-action on the ball preserves the invariant base measure. -/
theorem measurePreserving_ballGroupAction (g : Sp11) :
    MeasurePreserving (fun q : Ball => g • q) ballInvariantMeasure ballInvariantMeasure := by
  refine ⟨(continuous_ballGroupAction g).measurable, ?_⟩
  apply (MeasurableEmbedding.subtype_coe ball_isOpen.measurableSet).map_injective
  rw [Measure.map_map measurable_subtype_coe (continuous_ballGroupAction g).measurable]
  change Measure.map (mobiusPoint g ∘ (Subtype.val : Ball → ℍ)) ballInvariantMeasure = _
  rw [← Measure.map_map (measurable_mobiusPoint g) measurable_subtype_coe,
    map_ballInvariantMeasure, mobius_map_invariantBallMeasure g.property]

end MathResearch.Spinor
