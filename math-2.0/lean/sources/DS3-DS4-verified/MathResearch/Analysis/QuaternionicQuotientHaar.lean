module
public import MathResearch.Analysis.QuaternionicHaarMeasure

/-! The normalized quotient-Haar integration theorem, including integrability.
The proof uses Tonelli for nonnegative functions and compact-fibre integrability;
thus it also handles nonintegrable functions under Lean's totalized integral. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Quaternion ENNReal
open MeasureTheory MeasureTheory.Measure
namespace MathResearch.Spinor

theorem quotientHaarAverage_nonneg {φ : Sp11 → ℝ} (hφ : ∀ g, 0 ≤ φ g) (q : ℍ) :
    0 ≤ quotientHaarAverage φ q := by
  unfold quotientHaarAverage
  exact mul_nonneg (by positivity) (integral_nonneg fun k => hφ _)

theorem compactCoordinate_integrable {φ : Sp11 → ℝ} (hφ : Continuous φ) (q : Ball) :
    Integrable (fun k => φ (groupFromBallCoordinates (q,k))) compactHaar :=
  (hφ.comp (continuous_groupFromBallCoordinates.comp (continuous_const.prodMk continuous_id))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem quotientHaarAverage_aestronglyMeasurable {φ : Sp11 → ℝ} (hφ : Continuous φ) :
    AEStronglyMeasurable (quotientHaarAverage φ) (volume.restrict Ball) := by
  have hF : StronglyMeasurable (fun x : Ball × CompactPair => φ (groupFromBallCoordinates x)) :=
    (hφ.comp continuous_groupFromBallCoordinates).stronglyMeasurable
  have hc : StronglyMeasurable (fun q : Ball => quotientHaarAverage φ q) := by
    have h := continuous_invariantBallDensity_subtype.stronglyMeasurable.mul (hF.integral_prod_right' (ν := compactHaar))
    simpa only [quotientHaarAverage, invariantBallDensity, ballCompactPoint_eq_coordinates, Pi.mul_apply] using! h
  have hm : Measure.map (Subtype.val : Ball → ℍ) ballVolume = volume.restrict Ball :=
    map_comap_subtype_coe ball_isOpen.measurableSet volume
  rw [← hm]
  exact (MeasurableEmbedding.subtype_coe ball_isOpen.measurableSet).aestronglyMeasurable_map_iff.mpr hc.aestronglyMeasurable

/-- Tonelli's formula, before converting extended nonnegative integrals to real integrals. -/
theorem lintegral_quotientHaarAverage {φ : Sp11 → ℝ} (hφ : Continuous φ)
    (hpos : ∀ g, 0 ≤ φ g) :
    (∫⁻ g, ENNReal.ofReal (φ g) ∂normalizedGroupHaar) =
      ∫⁻ q in Ball, ENNReal.ofReal (quotientHaarAverage φ q) := by
  rw [lintegral_normalizedGroupHaar _ hφ.measurable.ennreal_ofReal]
  have hf : Measurable (fun q : Ball => ∫⁻ k : CompactPair,
      ENNReal.ofReal (φ (groupFromBallCoordinates (q,k))) ∂compactHaar) :=
    (hφ.measurable.ennreal_ofReal.comp continuous_groupFromBallCoordinates.measurable).lintegral_prod_right'
  unfold ballInvariantMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _
    continuous_invariantBallDensity_subtype.measurable.ennreal_ofReal
    hf]
  simp only [Pi.mul_apply]
  have he (q : Ball) :
      ENNReal.ofReal (invariantBallDensity q) *
        (∫⁻ k, ENNReal.ofReal (φ (groupFromBallCoordinates (q,k))) ∂compactHaar) =
      ENNReal.ofReal (quotientHaarAverage φ q) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (compactCoordinate_integrable hφ q)
      (Filter.Eventually.of_forall fun k => hpos _),
      ← ENNReal.ofReal_mul (invariantBallDensity_pos q.property).le]
    simp only [quotientHaarAverage, invariantBallDensity, ballCompactPoint_eq_coordinates]
  simp_rw [he]
  simpa only [ballVolume] using (lintegral_subtype_comap (μ := (volume : Measure ℍ))
    ball_isOpen.measurableSet (fun q => ENNReal.ofReal (quotientHaarAverage φ q)))

/-- The quotient formula detects integrability, as well as equality of integrals. -/
theorem integrable_quotientHaar_iff {φ : Sp11 → ℝ} (hφ : Continuous φ)
    (hpos : ∀ g, 0 ≤ φ g) :
    Integrable φ normalizedGroupHaar ↔ IntegrableOn (quotientHaarAverage φ) Ball volume := by
  have hG := hφ.aestronglyMeasurable (μ := normalizedGroupHaar)
  have hB := quotientHaarAverage_aestronglyMeasurable hφ
  simp only [IntegrableOn, Integrable, hG, hB, true_and]
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hpos),
    hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (quotientHaarAverage_nonneg hpos)),
    lintegral_quotientHaarAverage hφ hpos]

theorem integral_quotientHaar {φ : Sp11 → ℝ} (hφ : Continuous φ)
    (hpos : ∀ g, 0 ≤ φ g) :
    (∫ g, φ g ∂normalizedGroupHaar) = ∫ q in Ball, quotientHaarAverage φ q := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hpos) hφ.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (quotientHaarAverage_nonneg hpos))
      (quotientHaarAverage_aestronglyMeasurable hφ), lintegral_quotientHaarAverage hφ hpos]

/-- The exact background interface required by DS4, now proved separately. -/
theorem quotientHaarIntegration_proved : QuotientHaarIntegration normalizedGroupHaar where
  isHaar := normalizedGroupHaar_isHaar
  integrable_iff := fun _ hφ hpos => integrable_quotientHaar_iff hφ hpos
  integral_formula := fun _ hφ hpos => integral_quotientHaar hφ hpos

end MathResearch.Spinor
