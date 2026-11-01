module
public import MathResearch.Analysis.QuaternionicInvariantMeasure
public import Mathlib.MeasureTheory.Group.LIntegral

/-! Construction of normalized Haar measure on Sp(1,1) from B×K.
Left invariance is proved by the section cocycle, compact Haar invariance,
and the already established Möbius invariance of the base density. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Quaternion ENNReal
open MeasureTheory MeasureTheory.Measure
namespace MathResearch.Spinor

instance sp11T2Space : T2Space Sp11 := inferInstanceAs (T2Space {g : QuaternionMatrix2 // IsSp11 g})

instance compactHaar_isMulLeftInvariant : IsMulLeftInvariant compactHaar := by
  unfold compactHaar
  infer_instance
instance unitQuaternionHaar_isOpenPos : IsOpenPosMeasure unitQuaternionHaar := by
  unfold unitQuaternionHaar
  infer_instance
instance compactHaar_isOpenPos : IsOpenPosMeasure compactHaar := by
  unfold compactHaar
  infer_instance

/-- Haar normalization with dq/(1-|q|²)^4 on B and probability Haar on K. -/
def normalizedGroupHaar : Measure Sp11 :=
  Measure.map groupFromBallCoordinates (ballInvariantMeasure.prod compactHaar)

theorem lintegral_normalizedGroupHaar (f : Sp11 → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ g, f g ∂normalizedGroupHaar) =
      ∫⁻ q : Ball, ∫⁻ k : CompactPair, f (groupFromBallCoordinates (q,k))
        ∂compactHaar ∂ballInvariantMeasure := by
  rw [normalizedGroupHaar, lintegral_map hf continuous_groupFromBallCoordinates.measurable]
  exact lintegral_prod _ (hf.comp continuous_groupFromBallCoordinates.measurable).aemeasurable

instance normalizedGroupHaar_leftInvariant : IsMulLeftInvariant normalizedGroupHaar := by
  constructor
  intro g
  apply Measure.ext_of_lintegral
  intro f hf
  have hm : Measurable (fun h : Sp11 => g * h) := (continuous_const.mul continuous_id).measurable
  rw [lintegral_map hf hm,
    lintegral_normalizedGroupHaar _ (show Measurable (fun h => f (g*h)) from
      hf.comp (continuous_const.mul continuous_id).measurable),
    lintegral_normalizedGroupHaar f hf]
  simp_rw [group_coordinates_left_mul]
  have he (q : Ball) :
      (∫⁻ k, f (groupFromBallCoordinates (g • q, sectionCorrection g q * k)) ∂compactHaar) =
        ∫⁻ k, f (groupFromBallCoordinates (g • q,k)) ∂compactHaar :=
    lintegral_mul_left_eq_self (fun k => f (groupFromBallCoordinates (g • q,k))) _
  simp_rw [he]
  exact (measurePreserving_ballGroupAction g).lintegral_comp
    (hf.comp continuous_groupFromBallCoordinates.measurable).lintegral_prod_right'

instance normalizedGroupHaar_openPos : IsOpenPosMeasure normalizedGroupHaar :=
  continuous_groupFromBallCoordinates.isOpenPosMeasure_map
    groupBallHomeomorph.symm.surjective

instance normalizedGroupHaar_finiteOnCompacts : IsFiniteMeasureOnCompacts normalizedGroupHaar := by
  constructor
  intro K hK
  rw [normalizedGroupHaar, Measure.map_apply continuous_groupFromBallCoordinates.measurable
    hK.isClosed.measurableSet]
  have he : groupFromBallCoordinates ⁻¹' K = groupBallHomeomorph '' K := by
    ext x
    constructor
    · intro hx
      exact ⟨groupFromBallCoordinates x, hx, groupBallCoordinates_fromCoordinates x⟩
    · rintro ⟨g,hg,rfl⟩
      change groupFromBallCoordinates (groupBallCoordinates g) ∈ K
      simpa only [groupFromBallCoordinates_coordinates] using hg
  rw [he]
  exact (hK.image continuous_groupBallCoordinates).measure_lt_top

/-- The coordinate measure is a genuine Haar measure, with no external premise. -/
instance normalizedGroupHaar_isHaar : normalizedGroupHaar.IsHaarMeasure where

end MathResearch.Spinor
