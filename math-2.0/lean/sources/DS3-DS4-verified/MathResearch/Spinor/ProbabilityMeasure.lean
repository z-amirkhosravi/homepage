module
public import MathResearch.Spinor.WeakConstants
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-! The exact probability normalization in C6, by the canonical radial integral. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion ENNReal
open MeasureTheory MeasureTheory.Measure Set Metric
namespace MathResearch.Spinor

theorem quaternion_unitBall_volume : volume.real (ball (0 : ℍ) 1) = Real.pi^2 / 2 := by
  rw [Measure.real, InnerProductSpace.volume_ball_of_dim_even (k := 2)
    (by simpa using Quaternion.finrank_eq_four)]
  norm_num [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi^2 / 2)]

theorem radial_weight_integral (k : ℕ) :
    ∫ r in (0:ℝ)..1, r^3 * (1-r^2)^k = 1 / (2*(k+1:ℝ)*(k+2:ℝ)) := by
  let A : ℝ → ℝ := fun r => (1-r^2)^(k+2)/(2*(k+2:ℝ)) - (1-r^2)^(k+1)/(2*(k+1:ℝ))
  have hd (r : ℝ) : HasDerivAt A (r^3*(1-r^2)^k) r := by
    have h : HasDerivAt (fun x : ℝ => 1-x^2) (-2*r) r := by
      convert (hasDerivAt_const r (1:ℝ)).sub ((hasDerivAt_id r).pow 2) using 1
      · rfl
      · simp
    have H := ((h.pow (k+2)).div_const (2*(k+2:ℝ))).sub
      ((h.pow (k+1)).div_const (2*(k+1:ℝ)))
    change HasDerivAt A _ r at H
    convert H using 1
    simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
      show k+2-1=k+1 by omega, Nat.add_sub_cancel, pow_succ]
    field_simp
    ring
  have hi : IntervalIntegrable (fun r : ℝ => r^3*(1-r^2)^k) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) hi]
  norm_num [A, pow_succ]
  field_simp
  ring

theorem integral_ballScale_pow (k : ℕ) :
    ∫ q in Ball, ballScale q ^ k = Real.pi^2 / ((k+1:ℝ)*(k+2:ℝ)) := by
  let w : ℝ → ℝ := (Iio 1).indicator (fun r => (1-r^2)^k)
  have he : (∫ q in Ball, ballScale q^k) = ∫ q : ℍ, w ‖q‖ := by
    rw [← integral_indicator ball_isOpen.measurableSet]
    congr 1
    funext q
    by_cases hq : q ∈ Ball
    · simp only [indicator_of_mem hq, w, indicator_of_mem (show ‖q‖ ∈ Iio 1 from (mem_ball_iff q).mp hq),
        ballScale, Quaternion.normSq_eq_norm_mul_self, pow_two]
    · have hn : ¬ ‖q‖ < 1 := mt (mem_ball_iff q).mpr hq
      simp [w, indicator_of_notMem hq, hn]
  rw [he, integral_fun_norm_addHaar volume w]
  simp only [Quaternion.finrank_eq_four, Nat.reduceSub, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  have hr : (∫ r in Ioi (0:ℝ), r^3 * w r) = ∫ r in (0:ℝ)..1, r^3*(1-r^2)^k := by
    have hw : (fun r : ℝ => r^3 * w r) = (Iio 1).indicator (fun r => r^3*(1-r^2)^k) := by
      funext r
      by_cases h : r < 1 <;> simp [w, h]
    rw [hw, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [hr, radial_weight_integral, quaternion_unitBall_volume]
  field_simp
  ring

theorem integral_ballDensity (n : ℕ) (hn : 2 ≤ n) : ∫ q in Ball, ballDensity n q = 1 := by
  simp only [ballDensity, integral_const_mul]
  rw [integral_ballScale_pow]
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n:ℝ)-1 ≠ 0 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [weightConstant, Nat.cast_sub hn]
  norm_num only [Nat.cast_ofNat]
  rw [show (n:ℝ)-2+1=n-1 by ring, show (n:ℝ)-2+2=n by ring]
  field_simp [Real.pi_ne_zero, hn0, hn1]

/-- The actual previously defined weighted measure has total mass one. -/
theorem weightedBallMeasure_univ (n : ℕ) (hn : 2 ≤ n) : weightedBallMeasure n univ = 1 := by
  rw [weightedBallMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (ballDensity_integrable n)]
  · rw [integral_ballDensity n hn, ENNReal.ofReal_one]
  · filter_upwards [ae_restrict_mem ball_isOpen.measurableSet] with q hq
    exact (ballDensity_pos n hn hq).le

theorem weightedBallMeasure_isProbability (n : ℕ) (hn : 2 ≤ n) :
    IsProbabilityMeasure (weightedBallMeasure n) := ⟨weightedBallMeasure_univ n hn⟩

end MathResearch.Spinor
