module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Real, integer-weight Mellin identities with explicit absolute-convergence evidence. -/
@[expose] public section
noncomputable section
open scoped BigOperators Topology ENNReal
open MeasureTheory Set Real
namespace MathResearch.Fueter

/-- Mathlib's Gamma integral specialized to a natural power and positive rate. -/
theorem integral_pow_exp (n : ℕ) {b : ℝ} (hb : 0 < b) :
    ∫ t : ℝ in Ioi 0, t ^ n * exp (-b * t) = Gamma (n + 1) / b ^ (n + 1) := by
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (by positivity) hb
  simp only [add_sub_cancel_right, rpow_natCast] at h
  have he : (1 / b) ^ ((n : ℝ) + 1) = 1 / b ^ (n + 1) := by
    rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by simp, rpow_natCast, div_pow, one_pow]
  rw [he] at h
  simp only [neg_mul]
  exact h.trans (by ring)

theorem integrableOn_pow_exp (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ n * exp (-b * t)) (Ioi 0) := by
  simpa only [rpow_one, rpow_natCast] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1)
      (by linarith [Nat.cast_nonneg (α := ℝ) n]) zero_lt_one hb)

/-- A positive exponential dominates any fixed natural power, with an explicit constant. -/
theorem pow_mul_exp_neg_le (n : ℕ) {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    x ^ n * exp (-c * x) ≤ (n.factorial : ℝ) / c ^ n := by
  have h := pow_div_factorial_le_exp (c * x) (mul_nonneg hc.le hx.le) n
  have hfac : (0 : ℝ) < n.factorial := by positivity
  have hpow : (0 : ℝ) < c ^ n := pow_pos hc _
  rw [div_le_iff₀ hfac] at h
  rw [le_div_iff₀ hpow, neg_mul, exp_neg]
  have hh := mul_le_mul_of_nonneg_right h (inv_nonneg.mpr (exp_pos (c * x)).le)
  have he : exp (c * x) * (n.factorial : ℝ) * (exp (c * x))⁻¹ = n.factorial := by
    field_simp
  rw [he] at hh
  calc
    x ^ n * (exp (c * x))⁻¹ * c ^ n = (c * x) ^ n * (exp (c * x))⁻¹ := by rw [mul_pow]; ring
    _ ≤ n.factorial := hh

/-- A summable inverse-power coefficient bound gives pointwise absolute theta convergence. -/
theorem summable_exp_series {ι : Type*} {a b : ι → ℝ} (n : ℕ)
    (hb : ∀ i, 0 < b i) (hs : Summable (fun i => |a i| / b i ^ n))
    {t : ℝ} (ht : 0 < t) : Summable (fun i => a i * exp (-b i * t)) := by
  apply Summable.of_norm_bounded (hs.mul_right ((n.factorial : ℝ) / t ^ n))
  intro i
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
  have h := pow_mul_exp_neg_le n ht (hb i)
  calc
    |a i| * exp (-b i * t) = (|a i| / b i ^ n) * (b i ^ n * exp (-t * b i)) := by
      rw [show -b i * t = -t * b i by ring]
      field_simp [(hb i).ne']
    _ ≤ (|a i| / b i ^ n) * ((n.factorial : ℝ) / t ^ n) :=
      mul_le_mul_of_nonneg_left h (div_nonneg (abs_nonneg _) (pow_nonneg (hb i).le _))

/-- The absolute integral of a single weighted exponential. -/
theorem integral_norm_mellinTerm (n : ℕ) (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∫ t : ℝ in Ioi 0, ‖t ^ n * (a * exp (-b * t))‖ =
      Gamma (n + 1) * (|a| / b ^ (n + 1)) := by
  calc
    _ = ∫ t : ℝ in Ioi 0, |a| * (t ^ n * exp (-b * t)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg ht.le _),
        abs_of_pos (exp_pos _)]
      ring
    _ = _ := by rw [integral_const_mul, integral_pow_exp n hb]; ring

/-- Absolute convergence of the sum of integrals, the hypothesis used by mathlib's interchange. -/
theorem summable_integral_norm_mellin {ι : Type*} {a b : ι → ℝ} (n : ℕ)
    (hb : ∀ i, 0 < b i) (hs : Summable (fun i => |a i| / b i ^ (n + 1))) :
    Summable (fun i => ∫ t : ℝ in Ioi 0, ‖t ^ n * (a i * exp (-b i * t))‖) := by
  simpa only [integral_norm_mellinTerm n _ (hb _)] using hs.mul_left (Gamma (n + 1))

/-- A real series with summable absolute integrals has an integrable sum. -/
theorem integrable_real_tsum {ι α : Type*} [Countable ι] [MeasurableSpace α]
    {μ : Measure α} {F : ι → α → ℝ} (hm : ∀ i, Measurable (F i))
    (hi : ∀ i, Integrable (F i) μ)
    (hs : Summable (fun i => ∫ x, ‖F i x‖ ∂μ)) :
    Integrable (fun x => ∑' i, F i x) μ := by
  refine ⟨(Measurable.tsum hm).aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr ?_⟩
  calc
    ∫⁻ x, ‖∑' i, F i x‖ₑ ∂μ ≤ ∫⁻ x, ∑' i, ‖F i x‖ₑ ∂μ :=
      lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)
    _ = ∑' i, ∫⁻ x, ‖F i x‖ₑ ∂μ := lintegral_tsum (fun i => (hm i).enorm.aemeasurable)
    _ = ∑' i, ENNReal.ofReal (∫ x, ‖F i x‖ ∂μ) := by
      simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hi _)]
    _ < ∞ := hs.tsum_ofReal_lt_top

theorem integrableOn_mellin_series {ι : Type*} [Countable ι] {a b : ι → ℝ} (n : ℕ)
    (hb : ∀ i, 0 < b i) (hs : Summable (fun i => |a i| / b i ^ (n + 1))) :
    IntegrableOn (fun t : ℝ => t ^ n * (∑' i, a i * exp (-b i * t))) (Ioi 0) := by
  have hi (i : ι) : IntegrableOn (fun t : ℝ => t ^ n * (a i * exp (-b i * t))) (Ioi 0) := by
    simpa only [IntegrableOn, mul_left_comm (a i)] using
      (integrableOn_pow_exp n (hb i)).const_mul (a i)
  have hm (i : ι) : Measurable (fun t : ℝ => t ^ n * (a i * exp (-b i * t))) := by fun_prop
  simpa only [IntegrableOn, tsum_mul_left] using
    integrable_real_tsum hm hi (summable_integral_norm_mellin n hb hs)

/-- Mellin integration of a real exponential series; the input bound is absolute. -/
theorem real_mellin_series {ι : Type*} [Countable ι] {a b : ι → ℝ} (n : ℕ)
    (hb : ∀ i, 0 < b i) (hs : Summable (fun i => |a i| / b i ^ (n + 1))) :
    ∫ t : ℝ in Ioi 0, t ^ n * (∑' i, a i * exp (-b i * t)) =
      Gamma (n + 1) * (∑' i, a i / b i ^ (n + 1)) := by
  have hi (i : ι) : IntegrableOn (fun t : ℝ => t ^ n * (a i * exp (-b i * t))) (Ioi 0) := by
    simpa only [IntegrableOn, mul_left_comm (a i)] using (integrableOn_pow_exp n (hb i)).const_mul (a i)
  have he := (hasSum_integral_of_summable_integral_norm hi
    (summable_integral_norm_mellin n hb hs)).tsum_eq
  have ht (i : ι) : (∫ t : ℝ in Ioi 0, t ^ n * (a i * exp (-b i * t))) =
      Gamma (n + 1) * (a i / b i ^ (n + 1)) := by
    simp_rw [mul_left_comm _ (a i), integral_const_mul, integral_pow_exp n (hb i)]
    ring
  simp_rw [ht, tsum_mul_left] at he
  exact he.symm

end MathResearch.Fueter
