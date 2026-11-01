module
public import MathResearch.Spinor.RegularRowAction
public import MathResearch.Spinor.RowWeakEquation
public import MathResearch.Spinor.InteriorEvaluation
public import MathResearch.Spinor.ProbabilityMeasure
public import MathResearch.Spinor.LocalClosure

/-! DS2: the nonzero complete regular Hilbert models and their concrete
strongly continuous unitary actions. Here n=m+1, so the hypothesis m≥1 is n≥2.
Irreducibility and square-integrability of group coefficients (DS3/DS4) are separate. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Quaternion ContDiff
open MeasureTheory InnerProductSpace
namespace MathResearch.Spinor

/-- This completeness proof explicitly uses the canonical local L² limit argument. -/
theorem regularKernel_complete_by_localL2 (n : ℕ) (hn : 2 ≤ n) :
    CompleteSpace (WeakBallSpace n hn) :=
  (weakKernel_isClosed_by_localL2 n hn).completeSpace_coe

theorem regularRow_complete_by_localL2 (m : ℕ) (hm : 1 ≤ m) :
    CompleteSpace (weakRowKernel m hm) :=
  (weakSpinorIsometry m hm).toIsometryEquiv.completeSpace_iff.mp
    (regularKernel_complete_by_localL2 (m+1) (by omega))

theorem regularKernel_smooth_harmonic_classical (n : ℕ) (hn : 2 ≤ n) (f : WeakBallSpace n hn) :
    ∃ F : ℍ → BinaryForm n, ContDiffOn ℝ ∞ F Ball ∧ HarmonicOnNhd F Ball ∧
      (∀ q ∈ Ball, ∀ d, Fueter.leftOperator (fun x => fueterCoefficientCLM n d (F x)) q = 0) ∧
      (f.val : ℍ → BinaryForm n) =ᵐ[weightedBallMeasure n] F := by
  obtain ⟨F, hF, hH, he⟩ := weakKernel_smoothRepresentative n hn f
  exact ⟨F, hF, hH, (mem_weakKernel_iff_classicalFueter n hn f.val hF he).mp f.property, he⟩

theorem regularRow_smooth_harmonic_classical (m : ℕ) (hm : 1 ≤ m) (h : weakRowKernel m hm) :
    ∃ H : ℍ → CompatibleRow m, ContDiffOn ℝ ∞ H Ball ∧ HarmonicOnNhd H Ball ∧
      (∀ q ∈ Ball, ∀ d, Fueter.leftOperator (fun x => rowCoefficient m d (H x)) q = 0) ∧
      (h.val : ℍ → CompatibleRow m) =ᵐ[weightedBallMeasure (m+1)] H := by
  let f := (weakSpinorIsometry m hm).symm h
  obtain ⟨F, hF, hH, hD, he⟩ := regularKernel_smooth_harmonic_classical (m+1) (by omega) f
  let L := (spinorIsometry m).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  refine ⟨fun q => spinorIsometry m (F q), L.contDiff.comp_contDiffOn hF,
    hH.comp_CLM L, (row_fueter_iff m hF).mpr hD, ?_⟩
  have hs := weakSpinorIsometry_ae m hm f
  rw [show weakSpinorIsometry m hm f = h from (weakSpinorIsometry m hm).apply_symm_apply h] at hs
  filter_upwards [hs, he] with q hq hFq
  rw [hq, hFq]

/-- DS2/v1, with n=m+1. The actual unitary group homomorphisms, independently
specified row equation, smooth harmonic representatives, probability measure
and normalized intertwiner are all present. The continuity proof uses compact support. -/
theorem DS2_v1 (m : ℕ) (hm : 1 ≤ m) :
    CompleteSpace (WeakBallSpace (m+1) (by omega)) ∧
    Nontrivial (WeakBallSpace (m+1) (by omega)) ∧
    CompleteSpace (weakRowKernel m hm) ∧ Nontrivial (weakRowKernel m hm) ∧
    IsProbabilityMeasure (weightedBallMeasure (m+1)) ∧
    (∀ f : WeakBallSpace (m+1) (by omega),
      ∃ F : ℍ → BinaryForm (m+1), ContDiffOn ℝ ∞ F Ball ∧ HarmonicOnNhd F Ball ∧
        (∀ q ∈ Ball, ∀ d, Fueter.leftOperator (fun x => fueterCoefficientCLM (m+1) d (F x)) q = 0) ∧
        (f.val : ℍ → BinaryForm (m+1)) =ᵐ[weightedBallMeasure (m+1)] F) ∧
    (∀ h : weakRowKernel m hm,
      ∃ H : ℍ → CompatibleRow m, ContDiffOn ℝ ∞ H Ball ∧ HarmonicOnNhd H Ball ∧
        (∀ q ∈ Ball, ∀ d, Fueter.leftOperator (fun x => rowCoefficient m d (H x)) q = 0) ∧
        (h.val : ℍ → CompatibleRow m) =ᵐ[weightedBallMeasure (m+1)] H) ∧
    (∀ h : CompatibleBallL2 m, h ∈ weakRowKernel m hm ↔ RowDistributionRegular m h) ∧
    (∀ f : WeakBallSpace (m+1) (by omega),
      Continuous (fun g : Sp11 => regularRepresentation (m+1) (by omega) g f)) ∧
    (∀ h : weakRowKernel m hm, Continuous (fun g : Sp11 => regularRowRepresentation m hm g h)) ∧
    (∀ g : Sp11, ∀ f : WeakBallSpace (m+1) (by omega),
      regularRowRepresentation m hm g (weakSpinorIsometry m hm f) =
        weakSpinorIsometry m hm (regularRepresentation (m+1) (by omega) g f)) ∧
    (∀ g : Sp11, ∀ f : WeakBallSpace (m+1) (by omega),
      ((regularRepresentation (m+1) (by omega) g f).val : ℍ → BinaryForm (m+1)) =ᵐ[weightedBallMeasure (m+1)]
        ballRepresentation (m+1) g (f.val : ℍ → BinaryForm (m+1))) ∧
    (∀ g : Sp11, ∀ h : weakRowKernel m hm, ∀ᵐ q ∂weightedBallMeasure (m+1), ∀ k,
      quaternionCoefficients m (((regularRowRepresentation m hm g h).val q).val) k =
        rowBallRepresentation m g (fun x => quaternionCoefficients m ((h.val x).val)) q k) := by
  exact ⟨regularKernel_complete_by_localL2 (m+1) (by omega), inferInstance,
    regularRow_complete_by_localL2 m hm, inferInstance,
    weightedBallMeasure_isProbability (m+1) (by omega),
    regularKernel_smooth_harmonic_classical (m+1) (by omega),
    regularRow_smooth_harmonic_classical m hm, mem_weakRowKernel_iff_distribution m hm,
    stronglyContinuous_regularRepresentation_by_compact (m+1) (by omega),
    stronglyContinuous_regularRowRepresentation m hm,
    regularRow_intertwining m hm, (fun g f => weightedL2Action_ae (m+1) (by omega) g f.val),
    regularRowRepresentation_ae m hm⟩

end MathResearch.Spinor
