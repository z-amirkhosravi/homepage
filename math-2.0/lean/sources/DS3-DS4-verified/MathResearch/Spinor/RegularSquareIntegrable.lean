module
public import MathResearch.Spinor.RegularCoefficient
public import MathResearch.Spinor.CompactSchur

/-! DS4's Haar–Schur calculation for the actual regular Hilbert model.
Mean values and quotient Haar integration are explicit named background inputs;
compact Schur orthogonality is invoked from its separate verified module. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Quaternion ContDiff ENNReal
open MeasureTheory
namespace MathResearch.Spinor

/-- The squared-norm constant C13, with the specified Haar normalization. -/
def coefficientNormConstant (n : ℕ) (v : BinaryForm n) : ℝ :=
  ‖v‖^2 / ((n+1:ℝ)*weightConstant n)

theorem coefficientNormConstant_pos (n : ℕ) (hn : 2 ≤ n) (v : BinaryForm n) (hv : v ≠ 0) :
    0 < coefficientNormConstant n v :=
  div_pos (sq_pos_of_pos (norm_pos_iff.mpr hv)) (mul_pos (by positivity) (weightConstant_pos n hn))

theorem regularCoefficient_quotientAverage (meanValue : RadialMeanValueOnBall)
    (n : ℕ) (hn : 2 ≤ n) (hSchur : CompactSchurInput n compactHaar)
    (v : BinaryForm n) (f : WeakBallSpace n hn)
    (F : ℍ → BinaryForm n) (hF : ContDiffOn ℝ ∞ F Ball)
    (he : (f.val : ℍ → BinaryForm n) =ᵐ[weightedBallMeasure n] F)
    (q : ℍ) (hq : q ∈ Ball) :
    quotientHaarAverage (fun g => ‖regularCoefficient n hn v f g‖^2) q =
      coefficientNormConstant n v * (ballDensity n q * ‖F q‖^2) := by
  unfold quotientHaarAverage
  simp_rw [regularCoefficient_eq_lift meanValue n hn v f F hF he,
    liftedCoefficient, ballCompactPoint_coe q hq, fullLift_section_compact n F q hq]
  rw [hSchur, weightedSpinor, norm_smul, Real.norm_eq_abs,
    abs_of_pos (ballWeight_pos _ hq), mul_pow]
  have hc := (weightConstant_pos n hn).ne'
  calc
    _ = ((ballScale q)⁻¹ ^ 4 * (ballWeight (((n:ℝ)+2)/2) q)^2) * ‖F q‖^2 * ‖v‖^2 / (n+1:ℝ) := by ring
    _ = _ := by rw [lift_weight_cancellation n hn q hq]; unfold coefficientNormConstant ballDensity; field_simp

/-- Conversion of the weighted norm integrand to ordinary ball volume. -/
theorem weighted_square_integral (n : ℕ) (hn : 2 ≤ n) (F : ℍ → BinaryForm n) :
    (∫ q, ‖F q‖^2 ∂weightedBallMeasure n) = ∫ q in Ball, ballDensity n q * ‖F q‖^2 := by
  change (∫ q, ‖F q‖^2 ∂(volume.restrict Ball).withDensity (fun q => ENNReal.ofReal (ballDensity n q))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (continuous_ballDensity n).measurable.ennreal_ofReal (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply setIntegral_congr_fun ball_isOpen.measurableSet
  intro q hq
  simp [ENNReal.toReal_ofReal (ballDensity_pos n hn hq).le]

theorem weighted_square_integrable (n : ℕ) (hn : 2 ≤ n) (F : ℍ → BinaryForm n)
    (hi : Integrable (fun q => ‖F q‖^2) (weightedBallMeasure n)) :
    IntegrableOn (fun q => ballDensity n q * ‖F q‖^2) Ball volume := by
  have h := (integrable_withDensity_iff_integrable_smul'
    (continuous_ballDensity n).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hi
  apply h.congr
  filter_upwards [ae_restrict_mem ball_isOpen.measurableSet] with q hq
  simp [ENNReal.toReal_ofReal (ballDensity_pos n hn hq).le]

/-- Genuine square-integrability: the quotient theorem's integrability clause,
Schur orthogonality and the original weighted L² norm provide it. -/
theorem regularCoefficient_memLp (meanValue : RadialMeanValueOnBall)
    (n : ℕ) (hn : 2 ≤ n) (μG : Measure Sp11) (haar : QuotientHaarIntegration μG)
    (hSchur : CompactSchurInput n compactHaar) (v : BinaryForm n) (f : WeakBallSpace n hn) :
    MemLp (regularCoefficient n hn v f) 2 μG := by
  obtain ⟨F, hF, _, _, he⟩ := regularKernel_smooth_harmonic_classical n hn f
  have hm := (Lp.aestronglyMeasurable f.val).congr he
  have hLp := (Lp.memLp f.val).ae_eq he
  have hi := weighted_square_integrable n hn F ((memLp_two_iff_integrable_sq_norm hm).mp hLp)
  apply (memLp_two_iff_integrable_sq_norm (regularCoefficient_continuous n hn v f).aestronglyMeasurable).mpr
  apply (haar.integrable_iff _ ((regularCoefficient_continuous n hn v f).norm.pow 2)
    (fun _ => sq_nonneg _)).mpr
  apply (hi.const_mul (coefficientNormConstant n v)).congr
  filter_upwards [ae_restrict_mem ball_isOpen.measurableSet] with q hq
  exact (regularCoefficient_quotientAverage meanValue n hn hSchur v f F hF he q hq).symm

/-- C13 at the level of actual matrix coefficients, before choosing L² classes. -/
theorem regularCoefficient_integral (meanValue : RadialMeanValueOnBall)
    (n : ℕ) (hn : 2 ≤ n) (μG : Measure Sp11) (haar : QuotientHaarIntegration μG)
    (hSchur : CompactSchurInput n compactHaar) (v : BinaryForm n) (f : WeakBallSpace n hn) :
    (∫ g, ‖regularCoefficient n hn v f g‖^2 ∂μG) = coefficientNormConstant n v * ‖f‖^2 := by
  obtain ⟨F, hF, _, _, he⟩ := regularKernel_smooth_harmonic_classical n hn f
  rw [haar.integral_formula (fun g => ‖regularCoefficient n hn v f g‖^2) ((regularCoefficient_continuous n hn v f).norm.pow 2)
    (fun _ => sq_nonneg _)]
  calc
    _ = ∫ q in Ball, coefficientNormConstant n v * (ballDensity n q * ‖F q‖^2) := by
      apply setIntegral_congr_fun ball_isOpen.measurableSet
      exact regularCoefficient_quotientAverage meanValue n hn hSchur v f F hF he
    _ = coefficientNormConstant n v * ∫ q, ‖F q‖^2 ∂weightedBallMeasure n := by
      rw [integral_const_mul, weighted_square_integral n hn F]
    _ = coefficientNormConstant n v * ‖f‖^2 := by
      congr 1
      change _ = ‖f.val‖^2
      rw [l2_norm_sq_integral]
      exact integral_congr_ae (he.fun_comp (fun z => ‖z‖^2)).symm

/-- The actual L²-valued coefficient map; its square-integrability is proved above. -/
def regularCoefficientMap (meanValue : RadialMeanValueOnBall)
    (n : ℕ) (hn : 2 ≤ n) (μG : Measure Sp11) (haar : QuotientHaarIntegration μG)
    (hSchur : CompactSchurInput n compactHaar) (v : BinaryForm n) :
    WeakBallSpace n hn →ₗ[ℂ] Lp ℂ 2 μG where
  toFun f := (regularCoefficient_memLp meanValue n hn μG haar hSchur v f).toLp (regularCoefficient n hn v f)
  map_add' f h := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (regularCoefficient_memLp meanValue n hn μG haar hSchur v (f+h)),
      MemLp.coeFn_toLp (regularCoefficient_memLp meanValue n hn μG haar hSchur v f),
      MemLp.coeFn_toLp (regularCoefficient_memLp meanValue n hn μG haar hSchur v h),
      Lp.coeFn_add ((regularCoefficient_memLp meanValue n hn μG haar hSchur v f).toLp _)
        ((regularCoefficient_memLp meanValue n hn μG haar hSchur v h).toLp _)] with g hfh hf hh ha
    rw [hfh, ha]
    simp only [Pi.add_apply]
    rw [hf, hh]
    simp [regularCoefficient, map_add, inner_add_right]
  map_smul' z f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (regularCoefficient_memLp meanValue n hn μG haar hSchur v (z • f)),
      MemLp.coeFn_toLp (regularCoefficient_memLp meanValue n hn μG haar hSchur v f),
      Lp.coeFn_smul z ((regularCoefficient_memLp meanValue n hn μG haar hSchur v f).toLp _)] with g hzf hf hs
    simp only [RingHom.id_apply]
    rw [hzf, hs]
    simp only [Pi.smul_apply]
    rw [hf]
    simp [regularCoefficient, map_smul, inner_smul_right]

theorem regularCoefficientMap_ae (meanValue : RadialMeanValueOnBall)
    (n : ℕ) (hn : 2 ≤ n) (μG : Measure Sp11) (haar : QuotientHaarIntegration μG)
    (hSchur : CompactSchurInput n compactHaar) (v : BinaryForm n) (f : WeakBallSpace n hn) :
    (regularCoefficientMap meanValue n hn μG haar hSchur v f : Sp11 → ℂ) =ᵐ[μG]
      regularCoefficient n hn v f :=
  MemLp.coeFn_toLp (regularCoefficient_memLp meanValue n hn μG haar hSchur v f)

theorem regularCoefficientMap_norm (meanValue : RadialMeanValueOnBall)
    (n : ℕ) (hn : 2 ≤ n) (μG : Measure Sp11) (haar : QuotientHaarIntegration μG)
    (hSchur : CompactSchurInput n compactHaar) (v : BinaryForm n) (f : WeakBallSpace n hn) :
    ‖regularCoefficientMap meanValue n hn μG haar hSchur v f‖^2 = coefficientNormConstant n v * ‖f‖^2 := by
  rw [l2_norm_sq_integral, ← regularCoefficient_integral meanValue n hn μG haar hSchur v f]
  exact integral_congr_ae ((regularCoefficientMap_ae meanValue n hn μG haar hSchur v f).fun_comp (fun z => ‖z‖^2))

end MathResearch.Spinor
