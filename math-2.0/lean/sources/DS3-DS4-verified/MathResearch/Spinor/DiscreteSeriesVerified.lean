module
public import MathResearch.Spinor.DiscreteSeriesCoefficient
public import MathResearch.Analysis.QuaternionicRadialMeanValue
public import MathResearch.Analysis.QuaternionicQuotientHaar

/-! DS3–DS4 with the named background theorems supplied by their separate proofs.
The research argument remains the compact-averaging/orthogonal-complement proof
and the mean-value/Haar–Schur coefficient calculation in the internal notes. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open scoped Quaternion
open MeasureTheory
namespace MathResearch.Spinor

/-- DS3: topological irreducibility and density of the translates of constants. -/
theorem DS3_v1 (m : ℕ) (hm : 1 ≤ m) :
    TopologicallyIrreducible (regularRepresentation (m+1) (by omega)) ∧
      (translateSpan (regularRepresentation (m+1) (by omega))
        (LinearMap.range (constantRegularIsometry (m+1) (by omega)).toLinearMap)).topologicalClosure = ⊤ :=
  DS3_v1_of_meanValue sphericalMeanValueOnBall_proved m hm

/-- DS3 in the independently specified compatible-row model. -/
theorem DS3_row_v1 (m : ℕ) (hm : 1 ≤ m) :
    TopologicallyIrreducible (H := weakRowKernel m hm) (regularRowRepresentation m hm) ∧
      (translateSpan (H := weakRowKernel m hm) (regularRowRepresentation m hm)
        (LinearMap.range (constantRegularRowIsometry m hm).toLinearMap)).topologicalClosure = ⊤ :=
  ⟨DS3_row_of_meanValue sphericalMeanValueOnBall_proved m hm,
    DS3_row_dense_of_meanValue sphericalMeanValueOnBall_proved m hm⟩

/-- DS4: C12/C13 and an injective closed invariant coefficient image in genuine
Haar L². The Haar normalization and every background premise are now supplied. -/
theorem DS4_v1 (m : ℕ) (hm : 1 ≤ m) (v : BinaryForm (m+1)) (hv : v ≠ 0) :
    ∃ W : WeakBallSpace (m+1) (by omega) →ₗ[ℂ] Lp ℂ 2 normalizedGroupHaar,
      (∀ f, (W f : Sp11 → ℂ) =ᵐ[normalizedGroupHaar] regularCoefficient (m+1) (by omega) v f) ∧
      (∀ f, ‖W f‖^2 = coefficientNormConstant (m+1) v * ‖f‖^2) ∧
      Function.Injective W ∧ IsClosed (Set.range W) ∧
      (∀ a f, W (regularRepresentation (m+1) (by omega) a f) =
        leftL2Representation normalizedGroupHaar a (W f)) ∧
      UnitaryInvariant (leftL2Representation normalizedGroupHaar) (LinearMap.range W) :=
  DS4_v1_of_background radialMeanValueOnBall_proved m hm normalizedGroupHaar
    quotientHaarIntegration_proved v hv

/-- The normalized coefficient embedding of the actual polynomial model. -/
def DS4_polynomialEmbedding (m : ℕ) (hm : 1 ≤ m) (v : BinaryForm (m+1)) (hv : v ≠ 0) :
    WeakBallSpace (m+1) (by omega) →ₗᵢ[ℂ] Lp ℂ 2 normalizedGroupHaar :=
  regularCoefficientIsometry radialMeanValueOnBall_proved (m+1) (by omega)
    normalizedGroupHaar quotientHaarIntegration_proved (compactSchurInput_proved m) v hv

/-- The normalized coefficient embedding of the compatible-row model. -/
def DS4_rowEmbedding (m : ℕ) (hm : 1 ≤ m) (v : BinaryForm (m+1)) (hv : v ≠ 0) :
    weakRowKernel m hm →ₗᵢ[ℂ] Lp ℂ 2 normalizedGroupHaar :=
  regularRowCoefficientIsometry radialMeanValueOnBall_proved m hm normalizedGroupHaar
    quotientHaarIntegration_proved v hv

/-- DS4's closed isometric, intertwining embedding for the compatible-row model. -/
theorem DS4_row_v1 (m : ℕ) (hm : 1 ≤ m) (v : BinaryForm (m+1)) (hv : v ≠ 0) :
    IsClosed (Set.range (DS4_rowEmbedding m hm v hv)) ∧
      (∀ a f, DS4_rowEmbedding m hm v hv (regularRowRepresentation m hm a f) =
        leftL2Representation normalizedGroupHaar a (DS4_rowEmbedding m hm v hv f)) :=
  ⟨regularRowCoefficientIsometry_closed radialMeanValueOnBall_proved m hm normalizedGroupHaar
      quotientHaarIntegration_proved v hv,
    regularRowCoefficientIsometry_intertwines radialMeanValueOnBall_proved m hm normalizedGroupHaar
      quotientHaarIntegration_proved v hv⟩

/-- C13 for actual continuous matrix coefficients, including square-integrability. -/
theorem DS4_coefficient_formula (m : ℕ) (hm : 1 ≤ m) (v : BinaryForm (m+1))
    (f : WeakBallSpace (m+1) (by omega)) :
    MemLp (regularCoefficient (m+1) (by omega) v f) 2 normalizedGroupHaar ∧
      (∫ g, ‖regularCoefficient (m+1) (by omega) v f g‖^2 ∂normalizedGroupHaar) =
        coefficientNormConstant (m+1) v * ‖f‖^2 :=
  ⟨regularCoefficient_memLp radialMeanValueOnBall_proved (m+1) (by omega) normalizedGroupHaar
      quotientHaarIntegration_proved (compactSchurInput_proved m) v f,
    regularCoefficient_integral radialMeanValueOnBall_proved (m+1) (by omega) normalizedGroupHaar
      quotientHaarIntegration_proved (compactSchurInput_proved m) v f⟩

end MathResearch.Spinor
