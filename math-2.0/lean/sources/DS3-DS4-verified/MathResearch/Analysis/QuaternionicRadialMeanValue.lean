module
public import MathResearch.Analysis.QuaternionicMeanValue
public import MathResearch.Analysis.RotationalBallMeasure

/-! Radial probability mean values, by spherical averaging and Fubini.
Rotational invariance is the angular part of radial integration; the total mass
one was already proved by the explicit radial integral in ProbabilityMeasure. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Quaternion ContDiff
open MeasureTheory
namespace MathResearch.Spinor

/-- The exact radial mean-value dependency of DS3/DS4, with its L¹ hypothesis. -/
theorem radialMeanValueOnBall_proved : RadialMeanValueOnBall := by
  intro E _ _ _ n hn f hf hH hI
  let μ := weightedBallSubtypeMeasure n
  let F : Ball → E := fun q => f q
  let : IsProbabilityMeasure μ := weightedBallSubtypeMeasure_isProbability n hn
  have hF : Continuous F := hf.continuousOn.domRestrict
  have hi : Integrable F μ := by
    have H := (MeasurableEmbedding.subtype_coe ball_isOpen.measurableSet).integrable_map_iff
      (μ := μ) (g := f)
    rw [map_weightedBallSubtypeMeasure n] at H
    exact H.mp hI
  have hJ : Continuous (fun x : Fueter.UnitQuaternion × Ball => F (unitBallRotation x.1 x.2)) := by
    apply hF.comp
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have hInner (a : Fueter.UnitQuaternion) :
      (∫ q : Ball, F (unitBallRotation a q) ∂μ) = ∫ q : Ball, F q ∂μ :=
    (unitBallRotation_preserving n a).integral_comp (unitBallRotation a).measurableEmbedding F
  have hNorm (a : Fueter.UnitQuaternion) :
      (∫ q : Ball, ‖F (unitBallRotation a q)‖ ∂μ) = ∫ q : Ball, ‖F q‖ ∂μ :=
    (unitBallRotation_preserving n a).integral_comp (unitBallRotation a).measurableEmbedding (fun q => ‖F q‖)
  have hProd : Integrable (fun x : Fueter.UnitQuaternion × Ball => F (unitBallRotation x.1 x.2))
      (unitQuaternionHaar.prod μ) := by
    apply (integrable_prod_iff hJ.aestronglyMeasurable).mpr
    constructor
    · exact Filter.Eventually.of_forall fun a =>
        (unitBallRotation_preserving n a).integrable_comp_of_integrable hi
    · simpa only [hNorm] using
        (integrable_const (μ := unitQuaternionHaar) (∫ q : Ball, ‖F q‖ ∂μ))
  calc
    (∫ q, f q ∂weightedBallMeasure n) = ∫ q : Ball, F q ∂μ := by
      rw [← map_weightedBallSubtypeMeasure n]
      exact (MeasurableEmbedding.subtype_coe ball_isOpen.measurableSet).integral_map f
    _ = ∫ a : Fueter.UnitQuaternion, ∫ q : Ball, F (unitBallRotation a q) ∂μ ∂unitQuaternionHaar := by
      simp only [hInner, integral_const, probReal_univ, one_smul]
    _ = ∫ q : Ball, ∫ a : Fueter.UnitQuaternion, F (unitBallRotation a q) ∂unitQuaternionHaar ∂μ :=
      integral_integral_swap hProd
    _ = ∫ _q : Ball, f 0 ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro q
      exact sphericalAverage_harmonic hf hH q.property
    _ = f 0 := by simp

end MathResearch.Spinor
