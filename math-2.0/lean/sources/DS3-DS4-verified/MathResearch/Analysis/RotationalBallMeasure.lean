module
public import MathResearch.Analysis.QuaternionicInvariantMeasure
public import MathResearch.Analysis.QuaternionicSphericalAverage
public import MathResearch.Analysis.InvariantDensity
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Rotational invariance of the radial probability measure in DS3.
The subtype version permits compact averaging with functions continuous only
inside the ball; arbitrary outside values never enter the argument. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion ENNReal
open MeasureTheory MeasureTheory.Measure Set
namespace MathResearch.Spinor

def unitBallRotation (a : Fueter.UnitQuaternion) : Ball ≃ₜ Ball where
  toFun q := ⟨(a:ℍ)*q, unit_mul_mem_ball a q.property⟩
  invFun q := ⟨((a⁻¹ : Fueter.UnitQuaternion):ℍ)*q, unit_mul_mem_ball a⁻¹ q.property⟩
  left_inv q := by
    apply Subtype.ext
    change ((a⁻¹ : Fueter.UnitQuaternion):ℍ) * ((a:ℍ)*q) = q
    rw [Fueter.unitQuaternion_coe_inv, ← mul_assoc, Unitary.coe_star_mul_self, one_mul]
  right_inv q := by
    apply Subtype.ext
    change (a:ℍ) * (((a⁻¹ : Fueter.UnitQuaternion):ℍ)*q) = q
    rw [Fueter.unitQuaternion_coe_inv, ← mul_assoc, ← Unitary.coe_star, Unitary.coe_mul_star_self, one_mul]
  continuous_toFun := (continuous_const.mul continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_const.mul continuous_subtype_val).subtype_mk _

theorem ballDensity_unit_mul (n : ℕ) (a : Fueter.UnitQuaternion) (q : ℍ) :
    ballDensity n ((a:ℍ)*q) = ballDensity n q := by
  simp [ballDensity, ballScale, map_mul, Fueter.unitQuaternion_normSq]

theorem unitRotation_preserves_weightedBall (n : ℕ) (a : Fueter.UnitQuaternion) :
    MeasurePreserving (fun q : ℍ => (a:ℍ)*q) (weightedBallMeasure n) (weightedBallMeasure n) := by
  let L := Fueter.quaternionRotation (a,1)
  have he : L ⁻¹' Ball = Ball := by
    ext q
    simp only [mem_preimage, mem_ball_iff, L.norm_map]
  have hv : MeasurePreserving L (volume.restrict Ball) (volume.restrict Ball) := by
    have h := L.measurePreserving.restrict_preimage_emb L.toHomeomorph.measurableEmbedding Ball
    rwa [he] at h
  have hd := MathResearch.Analysis.measurePreserving_withDensity hv
    (continuous_ballDensity n).measurable.ennreal_ofReal
    (fun q => congrArg ENNReal.ofReal (show ballDensity n (L q) = ballDensity n q from by
      simpa [L, Fueter.quaternionRotation] using ballDensity_unit_mul n a q))
  simpa [weightedBallMeasure, L, Fueter.quaternionRotation] using hd

/-- The same radial measure on the open-ball subtype. -/
def weightedBallSubtypeMeasure (n : ℕ) : Measure Ball :=
  ballVolume.withDensity (fun q => ENNReal.ofReal (ballDensity n q))

theorem map_weightedBallSubtypeMeasure (n : ℕ) :
    Measure.map (Subtype.val : Ball → ℍ) (weightedBallSubtypeMeasure n) = weightedBallMeasure n := by
  rw [weightedBallSubtypeMeasure, MathResearch.Analysis.map_withDensity_comp ballVolume
    measurable_subtype_coe (continuous_ballDensity n).measurable.ennreal_ofReal,
    show Measure.map (Subtype.val : Ball → ℍ) ballVolume = volume.restrict Ball from
      map_comap_subtype_coe ball_isOpen.measurableSet volume]
  rfl

instance weightedBallSubtypeMeasure_finite (n : ℕ) : IsFiniteMeasure (weightedBallSubtypeMeasure n) := by
  constructor
  have h := congrArg (fun μ : Measure ℍ => μ univ) (map_weightedBallSubtypeMeasure n)
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ] at h
  rw [h]
  exact measure_lt_top _ _

theorem weightedBallSubtypeMeasure_isProbability (n : ℕ) (hn : 2 ≤ n) :
    IsProbabilityMeasure (weightedBallSubtypeMeasure n) := by
  constructor
  have h := congrArg (fun μ : Measure ℍ => μ univ) (map_weightedBallSubtypeMeasure n)
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ] at h
  rw [h, weightedBallMeasure_univ n hn]

theorem unitBallRotation_preserving (n : ℕ) (a : Fueter.UnitQuaternion) :
    MeasurePreserving (unitBallRotation a) (weightedBallSubtypeMeasure n) (weightedBallSubtypeMeasure n) := by
  refine ⟨(unitBallRotation a).measurable, ?_⟩
  apply (MeasurableEmbedding.subtype_coe ball_isOpen.measurableSet).map_injective
  rw [Measure.map_map measurable_subtype_coe (unitBallRotation a).measurable]
  change Measure.map ((fun q : ℍ => (a:ℍ)*q) ∘ (Subtype.val : Ball → ℍ)) _ = _
  have hm : Measurable (fun q : ℍ => (a:ℍ)*q) := (continuous_const.mul continuous_id).measurable
  rw [← Measure.map_map hm measurable_subtype_coe,
    map_weightedBallSubtypeMeasure, (unitRotation_preserves_weightedBall n a).map_eq]

end MathResearch.Spinor
