module
public import MathResearch.Spinor.RegularOrbit
public import MathResearch.Spinor.CompactIrreducible
public import MathResearch.Analysis.HarmonicMeanValue
public import MathResearch.Analysis.UnitaryIrreducible

/-! DS3 follows the internal proof: invoke spherical mean values, obtain a
nonzero constant in any nonzero closed invariant subspace, use compact
polynomial irreducibility, and apply the same argument to the orthogonal
complement. The unverified mean-value theorem remains an explicit hypothesis. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open scoped Quaternion ContDiff
open MeasureTheory
namespace MathResearch.Spinor

theorem regular_compact_average (meanValue : SphericalMeanValueOnBall)
    (n : ℕ) (hn : 2 ≤ n) (f : WeakBallSpace n hn) :
    (∫ a, regularRepresentation n hn (compactLeftSp11 a) f ∂unitQuaternionHaar) =
      constantRegularIsometry n hn (regularOrigin n hn f) := by
  obtain ⟨F, hF, hH, _, he⟩ := regularKernel_smooth_harmonic_classical n hn f
  apply regularEvaluation_ext n hn
  intro q hq
  rw [regularEvaluation_constant]
  rw [← (regularEvaluation n hn q hq).integral_comp_comm (compactRegularOrbit_integrable n hn f)]
  have hp (a : Fueter.UnitQuaternion) : regularEvaluation n hn q hq
      (regularRepresentation n hn (compactLeftSp11 a) f) = F ((a:ℍ)⁻¹*q) := by
    rw [regularEvaluation_action n hn _ f F hF he]
    change ballRepresentation n (compactSp11 (a,1)) F q = _
    simpa [quaternionMatrix_one] using ballRepresentation_compact n a 1 F q
  simp_rw [hp]
  rw [meanValue (BinaryForm n) F hF hH q hq]
  exact (regularEvaluation_eq_representative n hn 0 _ f hF.continuousOn he).symm

theorem regular_constant_orbit_spans (m : ℕ) (hm : 1 ≤ m) (v : BinaryForm (m+1)) (hv : v ≠ 0) :
    LinearMap.range (constantRegularIsometry (m+1) (by omega)).toLinearMap ≤
      Submodule.span ℂ (Set.range fun g : Sp11 =>
        regularRepresentation (m+1) (by omega) g (constantRegularIsometry (m+1) (by omega) v)) := by
  have hn : 2 ≤ m+1 := by omega
  exact equivariant_irreducible_range_le_span
    (regularRepresentation (m+1) hn) (constantRegularIsometry (m+1) hn)
    (fun a : Fueter.UnitQuaternion => polynomialRepresentation (m+1) (quaternionMatrix a))
    (fun a => compactSp11 (1,a))
    (fun a p => (regularAction_constant_compact (m+1) hn 1 a p).symm)
    (compactPolynomial_irreducible m) v hv

/-- All analytic/finite-dimensional inputs of the general Hilbert argument are
instantiated; the named spherical mean-value theorem is the only open input. -/
theorem regular_compactAveragingInputs (meanValue : SphericalMeanValueOnBall)
    (m : ℕ) (hm : 1 ≤ m) :
    CompactAveragingInputs (regularRepresentation (m+1) (by omega)) unitQuaternionHaar
      compactLeftSp11 (constantRegularIsometry (m+1) (by omega)) (regularOrigin (m+1) (by omega)) where
  average_integrable := compactRegularOrbit_integrable (m+1) (by omega)
  average_eq_constant := regular_compact_average meanValue (m+1) (by omega)
  translate_detects := regular_translate_detects (m+1) (by omega)
  constant_orbit_spans := regular_constant_orbit_spans m hm

/-- The actual DS3 polynomial model, conditional only on the explicitly named
unverified mean-value theorem. No replacement proof of that theorem is inserted. -/
theorem DS3_v1_of_meanValue (meanValue : SphericalMeanValueOnBall) (m : ℕ) (hm : 1 ≤ m) :
    TopologicallyIrreducible (regularRepresentation (m+1) (by omega)) ∧
      (translateSpan (regularRepresentation (m+1) (by omega))
        (LinearMap.range (constantRegularIsometry (m+1) (by omega)).toLinearMap)).topologicalClosure = ⊤ := by
  have hn : 2 ≤ m+1 := by omega
  let : Nontrivial (BinaryForm (m+1)) := (coefficientEquiv (m+1)).symm.injective.nontrivial
  have hi := DS3_irreducible_of_compactAveraging
    (regularRepresentation (m+1) hn) unitQuaternionHaar compactLeftSp11
    (constantRegularIsometry (m+1) hn) (regularOrigin (m+1) hn)
    (regular_compactAveragingInputs meanValue m hm)
  refine ⟨hi, DS3_dense_translateSpan hi _ ?_⟩
  intro hz
  obtain ⟨v, hv⟩ := exists_ne (0 : BinaryForm (m+1))
  have h : constantRegularIsometry (m+1) hn v ∈
      LinearMap.range (constantRegularIsometry (m+1) hn).toLinearMap := ⟨v, rfl⟩
  rw [hz, Submodule.mem_bot] at h
  exact hv ((constantRegularIsometry (m+1) hn).injective (h.trans (map_zero _).symm))

/-- The same irreducibility statement for the independently specified row model. -/
theorem DS3_row_of_meanValue (meanValue : SphericalMeanValueOnBall) (m : ℕ) (hm : 1 ≤ m) :
    TopologicallyIrreducible (H := weakRowKernel m hm) (regularRowRepresentation m hm) :=
  TopologicallyIrreducible.transport _ _ (weakSpinorIsometry m hm)
    (regularRow_intertwining m hm) (DS3_v1_of_meanValue meanValue m hm).1

/-- Constants transported through the normalized polynomial-to-row isometry. -/
def constantRegularRowIsometry (m : ℕ) (hm : 1 ≤ m) : BinaryForm (m+1) →ₗᵢ[ℂ] weakRowKernel m hm :=
  (weakSpinorIsometry m hm).toLinearIsometry.comp (constantRegularIsometry (m+1) (by omega))

theorem DS3_row_dense_of_meanValue (meanValue : SphericalMeanValueOnBall) (m : ℕ) (hm : 1 ≤ m) :
    (translateSpan (H := weakRowKernel m hm) (regularRowRepresentation m hm)
      (LinearMap.range (constantRegularRowIsometry m hm).toLinearMap)).topologicalClosure = ⊤ := by
  let : Nontrivial (BinaryForm (m+1)) := (coefficientEquiv (m+1)).symm.injective.nontrivial
  apply DS3_dense_translateSpan (DS3_row_of_meanValue meanValue m hm)
  intro hz
  obtain ⟨v, hv⟩ := exists_ne (0 : BinaryForm (m+1))
  have h : constantRegularRowIsometry m hm v ∈
      LinearMap.range (constantRegularRowIsometry m hm).toLinearMap := ⟨v, rfl⟩
  rw [hz, Submodule.mem_bot] at h
  exact hv ((constantRegularRowIsometry m hm).injective (h.trans (map_zero _).symm))

end MathResearch.Spinor
