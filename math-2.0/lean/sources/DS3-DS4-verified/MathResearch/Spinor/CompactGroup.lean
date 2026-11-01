module
public import MathResearch.Spinor.DiscreteSeriesModel
public import MathResearch.Spinor.CompactAveraging
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! The actual compact quaternion group, its normalized Haar measure, and
isometric constant vectors in the regular Hilbert model. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion ContDiff
open MeasureTheory
namespace MathResearch.Spinor

instance unitQuaternion_compactSpace : CompactSpace Fueter.UnitQuaternion := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_sphere (0 : ℍ) 1).of_isClosed_subset isClosed_unitary
  intro a ha
  simpa using Fueter.unitQuaternion_norm ⟨a, ha⟩

/-- Haar probability on the actual unit-quaternion group. -/
def unitQuaternionHaar : Measure Fueter.UnitQuaternion := Measure.haarMeasure ⊤
instance : IsProbabilityMeasure unitQuaternionHaar := ⟨by simpa [unitQuaternionHaar] using (Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts Fueter.UnitQuaternion)))⟩
instance : Measure.IsMulLeftInvariant unitQuaternionHaar := by unfold unitQuaternionHaar; infer_instance

/-- Product Haar probability on the two compact factors. -/
def compactHaar : Measure CompactPair := unitQuaternionHaar.prod unitQuaternionHaar
instance : IsProbabilityMeasure compactHaar := by unfold compactHaar; infer_instance

/-- The genuine compact block embedding is continuous. -/
theorem continuous_compactSp11 : Continuous compactSp11 := by
  apply Continuous.subtype_mk
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  fin_cases i <;> fin_cases j
  all_goals fun_prop [compactMatrix]

def compactLeftSp11 (a : Fueter.UnitQuaternion) : Sp11 := compactSp11 (a, 1)
def compactRightSp11 (a : Fueter.UnitQuaternion) : Sp11 := compactSp11 (1, a)

theorem continuous_compactLeftSp11 : Continuous compactLeftSp11 :=
  continuous_compactSp11.comp (continuous_id.prodMk continuous_const)
theorem continuous_compactRightSp11 : Continuous compactRightSp11 :=
  continuous_compactSp11.comp (continuous_const.prodMk continuous_id)

/-- The probability normalization turns the existing constant embedding into an isometry. -/
def constantRegularIsometry (n : ℕ) (hn : 2 ≤ n) :
    BinaryForm n →ₗᵢ[ℂ] WeakBallSpace n hn where
  toLinearMap := constantWeakEmbedding n hn
  norm_map' p := by
    let := weightedBallMeasure_isProbability n hn
    change ‖Lp.const 2 (weightedBallMeasure n) p‖ = ‖p‖
    rw [Lp.norm_const _ _ _ (by norm_num)]
    simp

/-- Integrability of the actual compact orbit in the regular Hilbert space. -/
theorem compactRegularOrbit_integrable (n : ℕ) (hn : 2 ≤ n) (f : WeakBallSpace n hn) :
    Integrable (fun a => regularRepresentation n hn (compactLeftSp11 a) f) unitQuaternionHaar :=
  ((stronglyContinuous_regularRepresentation_by_compact n hn f).comp
    continuous_compactLeftSp11).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end MathResearch.Spinor
