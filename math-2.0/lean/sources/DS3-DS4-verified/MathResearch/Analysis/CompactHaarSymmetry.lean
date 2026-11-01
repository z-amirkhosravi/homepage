module
public import MathResearch.Spinor.CompactGroup
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Right-translation and inversion invariance of the normalized compact Haar
measure. Both follow from mathlib's uniqueness theorem. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure
namespace MathResearch.Spinor

instance unitQuaternionHaar_isHaar : unitQuaternionHaar.IsHaarMeasure := by
  unfold unitQuaternionHaar
  infer_instance

private theorem unitQuaternionHaar_unique (ν : Measure Fueter.UnitQuaternion)
    [IsMulLeftInvariant ν] [IsProbabilityMeasure ν] : ν = unitQuaternionHaar := by
  have h := isMulInvariant_eq_smul_of_compactSpace ν unitQuaternionHaar
  have hc := congrArg (fun μ : Measure Fueter.UnitQuaternion => μ Set.univ) h
  simp only [measure_univ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_one] at hc
  rw [show haarScalarFactor ν unitQuaternionHaar = 1 from by exact_mod_cast hc.symm,
    one_smul] at h
  exact h

instance unitQuaternionHaar_rightInvariant : IsMulRightInvariant unitQuaternionHaar := by
  constructor
  intro a
  exact unitQuaternionHaar_unique _

instance unitQuaternionHaar_invInvariant : IsInvInvariant unitQuaternionHaar := by
  constructor
  let : IsProbabilityMeasure unitQuaternionHaar.inv := ⟨by
    rw [Measure.inv_def, Measure.map_apply measurable_inv MeasurableSet.univ]
    simp⟩
  exact unitQuaternionHaar_unique unitQuaternionHaar.inv

end MathResearch.Spinor
