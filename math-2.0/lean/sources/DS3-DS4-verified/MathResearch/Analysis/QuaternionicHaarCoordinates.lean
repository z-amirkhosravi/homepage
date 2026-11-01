module
public import MathResearch.Analysis.QuotientHaarIntegration
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! The global ball/compact coordinates for Sp(1,1). These are the geometric
input to the separate quotient-Haar theorem, not part of DS4's coefficient proof. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Quaternion Matrix.Norms.Elementwise
open MeasureTheory
namespace MathResearch.Spinor

/-- A quaternion of squared norm one as an actual unit-quaternion group element. -/
def unitQuaternionOfNormSq (q : ℍ) (hq : Quaternion.normSq q = 1) : Fueter.UnitQuaternion :=
  ⟨q, by
    constructor
    · rw [Quaternion.star_mul_self, hq, Quaternion.coe_one]
    · rw [Quaternion.self_mul_star, hq, Quaternion.coe_one]⟩

/-- The canonical section as a map to the actual matrix group. -/
def ballSectionPoint (q : Ball) : Sp11 := ⟨ballSection q, ballSection_isSp11 q q.property⟩

/-- The inverse coordinates g↦(g·0,k_L(g),k_R(g)). -/
def groupBallCoordinates (g : Sp11) : Ball × CompactPair :=
  (⟨groupOrigin g, groupOrigin_mem_ball g.property⟩,
    unitQuaternionOfNormSq (compactLeft g) (compactLeft_unit g.property),
    unitQuaternionOfNormSq (compactRight g) (compactRight_unit g.property))

def groupFromBallCoordinates (x : Ball × CompactPair) : Sp11 :=
  ballSectionPoint x.1 * compactSp11 x.2

@[simp] theorem compactSp11_mul (k l : CompactPair) : compactSp11 (k*l) = compactSp11 k * compactSp11 l :=
  Subtype.ext (compactMatrix_mul _ _ _ _).symm

@[simp] theorem compactSp11_one : compactSp11 1 = 1 := by
  apply Subtype.ext
  simp [compactSp11, compactMatrix, Matrix.one_fin_two]

/-- The unit-quaternion factors form a group embedding. -/
def compactSp11Hom : CompactPair →* Sp11 where
  toFun := compactSp11
  map_one' := compactSp11_one
  map_mul' := compactSp11_mul

theorem compactSp11_injective : Function.Injective compactSp11 := by
  intro k l h
  have he := congrArg (fun g : Sp11 => (g : QuaternionMatrix2)) h
  apply Prod.ext
  · exact Subtype.ext (congrArg (fun M : QuaternionMatrix2 => M 0 0) he)
  · exact Subtype.ext (congrArg (fun M : QuaternionMatrix2 => M 1 1) he)

@[simp] theorem groupFromBallCoordinates_coordinates (g : Sp11) :
    groupFromBallCoordinates (groupBallCoordinates g) = g := by
  apply Subtype.ext
  exact (section_compact_decomposition g.property).symm

@[simp] theorem groupBallCoordinates_fromCoordinates (x : Ball × CompactPair) :
    groupBallCoordinates (groupFromBallCoordinates x) = x := by
  have ho : groupOrigin (groupFromBallCoordinates x) = x.1 := by
    change groupOrigin (ballSection x.1 * compactMatrix x.2.1 x.2.2) = _
    rw [groupOrigin_compact_mul _ _ _ (Quaternion.normSq_ne_zero.mp (by rw [Fueter.unitQuaternion_normSq]; norm_num)), groupOrigin_ballSection _ x.1.property]
  apply Prod.ext
  · exact Subtype.ext ho
  · apply compactSp11_injective
    have h := groupFromBallCoordinates_coordinates (groupFromBallCoordinates x)
    change ballSectionPoint (groupBallCoordinates (groupFromBallCoordinates x)).1 *
      compactSp11 (groupBallCoordinates (groupFromBallCoordinates x)).2 =
        ballSectionPoint x.1 * compactSp11 x.2 at h
    have hq : (groupBallCoordinates (groupFromBallCoordinates x)).1 = x.1 := Subtype.ext ho
    rw [hq] at h
    exact mul_left_cancel h

theorem continuous_groupOrigin_on_group : Continuous (fun g : Sp11 => groupOrigin g) := by
  apply continuous_iff_continuousAt.mpr
  intro g
  exact (differentiableAt_groupOrigin g.property.lowerRight_ne_zero).continuousAt.comp
    continuous_subtype_val.continuousAt

theorem continuous_ballSectionPoint : Continuous ballSectionPoint := by
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro q
  exact (contDiffAt_ballSection q.property).continuousAt.comp continuous_subtype_val.continuousAt

theorem continuous_groupBallCoordinates : Continuous groupBallCoordinates := by
  have hs := Real.continuous_sqrt.comp (contDiff_ballScale.continuous.comp continuous_groupOrigin_on_group)
  apply Continuous.prodMk
  · exact continuous_groupOrigin_on_group.subtype_mk _
  · apply Continuous.prodMk <;> apply Continuous.subtype_mk
    · exact hs.smul ((continuous_apply 0).comp ((continuous_apply 0).comp continuous_subtype_val))
    · exact hs.smul ((continuous_apply 1).comp ((continuous_apply 1).comp continuous_subtype_val))

theorem continuous_groupFromBallCoordinates : Continuous groupFromBallCoordinates :=
  (continuous_ballSectionPoint.comp continuous_fst).mul (continuous_compactSp11.comp continuous_snd)

/-- G is homeomorphic to B×K through the specified section and compact factors. -/
def groupBallHomeomorph : Sp11 ≃ₜ Ball × CompactPair where
  toFun := groupBallCoordinates
  invFun := groupFromBallCoordinates
  left_inv := groupFromBallCoordinates_coordinates
  right_inv := groupBallCoordinates_fromCoordinates
  continuous_toFun := continuous_groupBallCoordinates
  continuous_invFun := continuous_groupFromBallCoordinates

/-- The already used ambient section agrees with the subtype coordinates on B. -/
theorem ballCompactPoint_eq_coordinates (q : Ball) (k : CompactPair) :
    ballCompactPoint q k = groupFromBallCoordinates (q,k) := by
  apply Subtype.ext
  simp only [ballCompactPoint_coe _ q.property, groupFromBallCoordinates, Sp11.coe_mul, ballSectionPoint]

/-- The compact correction in the action on section coordinates. -/
def sectionCorrection (g : Sp11) (q : Ball) : CompactPair :=
  (groupBallCoordinates (g * ballSectionPoint q)).2

theorem section_product_coordinates (g : Sp11) (q : Ball) :
    (groupBallCoordinates (g * ballSectionPoint q)).1 = g • q := by
  apply Subtype.ext
  exact groupOrigin_section_product g q q.property

theorem section_product_factorization (g : Sp11) (q : Ball) :
    g * ballSectionPoint q = ballSectionPoint (g • q) * compactSp11 (sectionCorrection g q) := by
  have h := groupFromBallCoordinates_coordinates (g * ballSectionPoint q)
  change ballSectionPoint (groupBallCoordinates (g * ballSectionPoint q)).1 *
    compactSp11 (sectionCorrection g q) = g * ballSectionPoint q at h
  rw [section_product_coordinates] at h
  exact h.symm

/-- Left translation is a base Möbius action followed by a compact left translation. -/
theorem group_coordinates_left_mul (g : Sp11) (q : Ball) (k : CompactPair) :
    g * groupFromBallCoordinates (q,k) =
      groupFromBallCoordinates (g • q, sectionCorrection g q * k) := by
  change g * (ballSectionPoint q * compactSp11 k) =
    ballSectionPoint (g • q) * compactSp11 (sectionCorrection g q * k)
  rw [← mul_assoc, section_product_factorization, compactSp11_mul, mul_assoc]

theorem continuous_ballGroupAction (g : Sp11) : Continuous (fun q : Ball => g • q) := by
  have hc : Continuous (fun q : Ball => g * ballSectionPoint q) :=
    continuous_const.mul continuous_ballSectionPoint
  have h := (continuous_groupBallCoordinates.comp hc).fst
  simpa only [Function.comp_apply, section_product_coordinates] using h

theorem continuous_sectionCorrection (g : Sp11) : Continuous (sectionCorrection g) :=
  (continuous_groupBallCoordinates.comp (continuous_const.mul continuous_ballSectionPoint)).snd

end MathResearch.Spinor
