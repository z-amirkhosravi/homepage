module
public import MathResearch.Spinor.RegularSquareIntegrable
public import MathResearch.Spinor.DiscreteSeriesIrreducible
public import MathResearch.Analysis.LeftRegularL2

/-! The conditional DS4 conclusion: C12/C13, a closed invariant coefficient
image in the actual Haar L² space, and normalized isometric embeddings in both
models. The unverified background theorems remain explicit parameters. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open scoped Quaternion
open MeasureTheory
namespace MathResearch.Spinor

section GeneralDegree
variable (meanValue : RadialMeanValueOnBall) (n : ℕ) (hn : 2 ≤ n)
    (μG : Measure Sp11) (haar : QuotientHaarIntegration μG)
    (hSchur : CompactSchurInput n compactHaar) (v : BinaryForm n)

/-- C12 intertwining after passage to genuine L² equivalence classes. -/
theorem regularCoefficientMap_intertwines (a : Sp11) (f : WeakBallSpace n hn) :
    let : μG.IsHaarMeasure := haar.isHaar
    regularCoefficientMap meanValue n hn μG haar hSchur v (regularRepresentation n hn a f) =
      leftL2Representation μG a (regularCoefficientMap meanValue n hn μG haar hSchur v f) := by
  let : μG.IsHaarMeasure := haar.isHaar
  apply Lp.ext
  filter_upwards [regularCoefficientMap_ae meanValue n hn μG haar hSchur v (regularRepresentation n hn a f),
    leftL2Translation_ae μG a (regularCoefficientMap meanValue n hn μG haar hSchur v f),
    (measurePreserving_mul_left μG a⁻¹).quasiMeasurePreserving.ae
      (regularCoefficientMap_ae meanValue n hn μG haar hSchur v f)] with g ha ht hf
  change _ = leftL2Translation μG a (regularCoefficientMap meanValue n hn μG haar hSchur v f) g
  rw [ha, ht, hf]
  exact regularCoefficient_intertwines n hn v f a g

/-- The fixed scalar normalization of the actual coefficient map. -/
def regularCoefficientIsometry (hv : v ≠ 0) : WeakBallSpace n hn →ₗᵢ[ℂ] Lp ℂ 2 μG :=
  normalizedCoefficientEmbedding μG (regularCoefficientMap meanValue n hn μG haar hSchur v)
    (coefficientNormConstant n v) (coefficientNormConstant_pos n hn v hv)
    (regularCoefficientMap_norm meanValue n hn μG haar hSchur v)

theorem regularCoefficientIsometry_intertwines (hv : v ≠ 0) (a : Sp11) (f : WeakBallSpace n hn) :
    let : μG.IsHaarMeasure := haar.isHaar
    regularCoefficientIsometry meanValue n hn μG haar hSchur v hv (regularRepresentation n hn a f) =
      leftL2Representation μG a (regularCoefficientIsometry meanValue n hn μG haar hSchur v hv f) := by
  let : μG.IsHaarMeasure := haar.isHaar
  change (Real.sqrt (coefficientNormConstant n v))⁻¹ •
      regularCoefficientMap meanValue n hn μG haar hSchur v (regularRepresentation n hn a f) =
    leftL2Representation μG a ((Real.sqrt (coefficientNormConstant n v))⁻¹ •
      regularCoefficientMap meanValue n hn μG haar hSchur v f)
  rw [regularCoefficientMap_intertwines]
  exact ((leftL2Representation μG a).toLinearEquiv.toLinearMap.map_smul_of_tower _ _).symm

end GeneralDegree

/-- DS4's actual polynomial-model coefficient embedding, with only the two named
unverified background statements. Schur orthogonality is supplied by its proof. -/
theorem DS4_v1_of_background (meanValue : RadialMeanValueOnBall)
    (m : ℕ) (hm : 1 ≤ m) (μG : Measure Sp11) (haar : QuotientHaarIntegration μG)
    (v : BinaryForm (m+1)) (hv : v ≠ 0) :
    let : μG.IsHaarMeasure := haar.isHaar
    ∃ W : WeakBallSpace (m+1) (by omega) →ₗ[ℂ] Lp ℂ 2 μG,
      (∀ f, (W f : Sp11 → ℂ) =ᵐ[μG] regularCoefficient (m+1) (by omega) v f) ∧
      (∀ f, ‖W f‖^2 = coefficientNormConstant (m+1) v * ‖f‖^2) ∧
      Function.Injective W ∧ IsClosed (Set.range W) ∧
      (∀ a f, W (regularRepresentation (m+1) (by omega) a f) = leftL2Representation μG a (W f)) ∧
      UnitaryInvariant (leftL2Representation μG) (LinearMap.range W) := by
  let : μG.IsHaarMeasure := haar.isHaar
  have hn : 2 ≤ m+1 := by omega
  let W := regularCoefficientMap meanValue (m+1) hn μG haar (compactSchurInput_proved m) v
  have hc := coefficientEmbedding_closed_range μG W (coefficientNormConstant (m+1) v)
    (coefficientNormConstant_pos (m+1) hn v hv)
    (regularCoefficientMap_norm meanValue (m+1) hn μG haar (compactSchurInput_proved m) v)
  have he : ∀ a f, W (regularRepresentation (m+1) hn a f) = leftL2Representation μG a (W f) :=
    regularCoefficientMap_intertwines meanValue (m+1) hn μG haar (compactSchurInput_proved m) v
  refine ⟨W, regularCoefficientMap_ae meanValue (m+1) hn μG haar (compactSchurInput_proved m) v,
    regularCoefficientMap_norm meanValue (m+1) hn μG haar (compactSchurInput_proved m) v,
    hc.1, hc.2, he, ?_⟩
  rintro a _ ⟨f, rfl⟩
  exact ⟨regularRepresentation (m+1) hn a f, he a f⟩

/-- The normalized DS4 embedding transported to the compatible-row model. -/
def regularRowCoefficientIsometry (meanValue : RadialMeanValueOnBall)
    (m : ℕ) (hm : 1 ≤ m) (μG : Measure Sp11) (haar : QuotientHaarIntegration μG)
    (v : BinaryForm (m+1)) (hv : v ≠ 0) : weakRowKernel m hm →ₗᵢ[ℂ] Lp ℂ 2 μG :=
  (regularCoefficientIsometry meanValue (m+1) (by omega) μG haar (compactSchurInput_proved m) v hv).comp
    (weakSpinorIsometry m hm).symm.toLinearIsometry

theorem regularRowCoefficientIsometry_intertwines (meanValue : RadialMeanValueOnBall)
    (m : ℕ) (hm : 1 ≤ m) (μG : Measure Sp11) (haar : QuotientHaarIntegration μG)
    (v : BinaryForm (m+1)) (hv : v ≠ 0) (a : Sp11) (f : weakRowKernel m hm) :
    let : μG.IsHaarMeasure := haar.isHaar
    regularRowCoefficientIsometry meanValue m hm μG haar v hv (regularRowRepresentation m hm a f) =
      leftL2Representation μG a (regularRowCoefficientIsometry meanValue m hm μG haar v hv f) := by
  let : μG.IsHaarMeasure := haar.isHaar
  have hn : 2 ≤ m+1 := by omega
  exact intertwiningIsometry_transport
    (regularRepresentation (m+1) hn) (regularRowRepresentation m hm) (leftL2Representation μG)
    (weakSpinorIsometry m hm)
    (regularCoefficientIsometry meanValue (m+1) hn μG haar (compactSchurInput_proved m) v hv)
    (regularRow_intertwining m hm)
    (regularCoefficientIsometry_intertwines meanValue (m+1) hn μG haar (compactSchurInput_proved m) v hv) a f

/-- Closed image of the actual normalized row embedding. -/
theorem regularRowCoefficientIsometry_closed (meanValue : RadialMeanValueOnBall)
    (m : ℕ) (hm : 1 ≤ m) (μG : Measure Sp11) (haar : QuotientHaarIntegration μG)
    (v : BinaryForm (m+1)) (hv : v ≠ 0) :
    IsClosed (Set.range (regularRowCoefficientIsometry meanValue m hm μG haar v hv)) :=
  (regularRowCoefficientIsometry meanValue m hm μG haar v hv).isometry.isClosedEmbedding.isClosed_range

end MathResearch.Spinor
