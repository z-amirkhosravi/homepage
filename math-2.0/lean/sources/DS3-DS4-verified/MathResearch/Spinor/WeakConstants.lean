module
public import MathResearch.Spinor.WeakKernel
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! Nonzero constant vectors in the weak Hilbert kernel, proved by integration by parts. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Quaternion BigOperators ENNReal
open MeasureTheory
namespace MathResearch.Spinor

theorem ballDensity_integrable (n : ℕ) : IntegrableOn (ballDensity n) Ball := by
  have h := (continuous_ballDensity n).continuousOn.integrableOn_compact (μ := volume) (isCompact_closedBall (0 : ℍ) 1)
  apply h.mono_set
  intro q hq
  simpa only [Metric.mem_closedBall, dist_zero_right] using ((mem_ball_iff q).mp hq).le

instance weightedBallMeasure_finite (n : ℕ) : IsFiniteMeasure (weightedBallMeasure n) :=
  isFiniteMeasure_withDensity (ballDensity_integrable n).lintegral_lt_top.ne

/-- The L² weak test is exactly the ordinary Lebesgue distributional test of the symbol. -/
theorem weakTest_toLp (n : ℕ) (hn : 2 ≤ n) (φ : BallTest) (j : Fin 2) (d : Fin 2 →₀ ℕ)
    (F : ℍ → BinaryForm n) (hF : MemLp F 2 (weightedBallMeasure n)) :
    weakTest n hn φ j d (hF.toLp F) =
      ∫ q in Ball, ∑ μ : Fin 4, (fderiv ℝ φ q (Fueter.coordinateBasis μ) : ℂ) * weakSymbol n μ j d (F q) := by
  change inner ℂ ((weakTestVector_memLp n hn φ j d).toLp (weakTestVector n φ j d)) (hF.toLp F) = _
  rw [L2.inner_def]
  calc
    _ = ∫ q, inner ℂ (weakTestVector n φ j d q) (F q) ∂weightedBallMeasure n := by
      apply integral_congr_ae
      filter_upwards [(weakTestVector_memLp n hn φ j d).coeFn_toLp, hF.coeFn_toLp] with q hq hq'
      rw [hq, hq']
    _ = _ := ?_
  change (∫ q, inner ℂ (weakTestVector n φ j d q) (F q)
    ∂(volume.restrict Ball).withDensity (fun q => ENNReal.ofReal (ballDensity n q))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (continuous_ballDensity n).measurable.ennreal_ofReal (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply setIntegral_congr_fun ball_isOpen.measurableSet
  intro q hq
  dsimp only
  rw [ENNReal.toReal_ofReal (ballDensity_pos n hn hq).le]
  exact weakTestVector_pairing n hn φ j d (F q) hq

theorem test_directional_integral_zero (φ : BallTest) (v : ℍ) :
    (∫ q in Ball, fderiv ℝ φ q v) = 0 := by
  have hc : Continuous (fun q => fderiv ℝ φ q v) :=
    (φ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi : Integrable (fun q => fderiv ℝ φ q v) :=
    hc.integrable_of_hasCompactSupport (φ.hasCompactSupport.fderiv_apply ℝ v)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun _ : ℍ => (1:ℝ)) (g := fun q => φ q) (v := v)
    (by simp)
    (by simpa using hi)
    (by simpa using φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)
    (fun _ _ => differentiableAt_const _) (fun q _ => φ.contDiff.differentiable (by simp) q)
  have hz : (∫ q, fderiv ℝ φ q v) = 0 := by simpa using h
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero, hz]
  intro q hq
  exact image_eq_zero_of_notMem_tsupport (f := fun q => fderiv ℝ φ q v)
    (fun hh => hq (φ.tsupport_subset ((tsupport_fderiv_apply_subset ℝ v) hh)))

theorem constant_mem_weakKernel (n : ℕ) (hn : 2 ≤ n) (p : BinaryForm n) :
    Lp.const 2 (weightedBallMeasure n) p ∈ weakKernel n hn := by
  rw [mem_weakKernel]
  intro φ j d
  rw [← MemLp.toLp_const, weakTest_toLp]
  have hi (μ : Fin 4) : IntegrableOn
      (fun q => (fderiv ℝ φ q (Fueter.coordinateBasis μ) : ℂ) * weakSymbol n μ j d p) Ball := by
    have hiR : Integrable (fun q => fderiv ℝ φ q (Fueter.coordinateBasis μ)) :=
      ((φ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
        (φ.hasCompactSupport.fderiv_apply ℝ _)
    exact (hiR.ofReal.mul_const _).integrableOn
  rw [integral_finsetSum _ (fun μ _ => hi μ)]
  apply Finset.sum_eq_zero
  intro μ _
  rw [integral_mul_const]
  have hcast : (∫ q in Ball, (fderiv ℝ φ q (Fueter.coordinateBasis μ) : ℂ)) = 0 := by
    calc
      _ = ((∫ q in Ball, fderiv ℝ φ q (Fueter.coordinateBasis μ) : ℝ) : ℂ) := integral_ofReal
      _ = 0 := by rw [test_directional_integral_zero]; rfl
  rw [hcast, zero_mul]

/-- The positive weight has exactly the same null sets as Lebesgue measure inside the ball. -/
theorem ae_weightedBall_iff (n : ℕ) (hn : 2 ≤ n) (P : ℍ → Prop) :
    (∀ᵐ q ∂weightedBallMeasure n, P q) ↔ ∀ᵐ q ∂volume.restrict Ball, P q := by
  unfold weightedBallMeasure
  rw [ae_withDensity_iff (continuous_ballDensity n).measurable.ennreal_ofReal]
  constructor
  · intro h
    filter_upwards [h, ae_restrict_mem ball_isOpen.measurableSet] with q hq hB
    exact hq (ENNReal.ofReal_ne_zero_iff.mpr (ballDensity_pos n hn hB))
  · intro h
    exact h.mono fun _ hq _ => hq

theorem weightedBallMeasure_ne_zero (n : ℕ) (hn : 2 ≤ n) : weightedBallMeasure n ≠ 0 := by
  intro hz
  have hfalse : ∀ᵐ q ∂weightedBallMeasure n, False := by rw [hz]; simp
  have he := (ae_weightedBall_iff n hn (fun _ => False)).mp hfalse
  have hb : (volume : Measure ℍ) Ball ≠ 0 :=
    (ball_isOpen.measure_pos volume ⟨0, by simp [Ball, ballScale]⟩).ne'
  simp [Measure.restrict_eq_zero, hb] at he

/-- Constants provide a concrete complex-linear injection into the weak kernel. -/
def constantWeakEmbedding (n : ℕ) (hn : 2 ≤ n) : BinaryForm n →ₗ[ℂ] WeakBallSpace n hn :=
  (Lp.constₗ 2 (weightedBallMeasure n) ℂ : BinaryForm n →ₗ[ℂ] BallL2 n).codRestrict (weakKernel n hn)
    (constant_mem_weakKernel n hn)

theorem constantWeakEmbedding_injective (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (constantWeakEmbedding n hn) := by
  let : NeZero (weightedBallMeasure n) := ⟨weightedBallMeasure_ne_zero n hn⟩
  intro p r h
  have hh : Lp.const 2 (weightedBallMeasure n) p = Lp.const 2 (weightedBallMeasure n) r :=
    congrArg Subtype.val h
  have ha : ∀ᵐ _q ∂weightedBallMeasure n, p = r := by
    filter_upwards [(memLp_const (p := 2) (μ := weightedBallMeasure n) p).coeFn_toLp,
      (memLp_const (p := 2) (μ := weightedBallMeasure n) r).coeFn_toLp] with q hp hr
    exact hp.symm.trans ((congrArg (fun f : BallL2 n => f q) hh).trans hr)
  exact ha.exists.choose_spec

instance weakBallSpace_nontrivial (n : ℕ) (hn : 2 ≤ n) : Nontrivial (WeakBallSpace n hn) :=
  let : Nontrivial (BinaryForm n) := (coefficientEquiv n).symm.injective.nontrivial
  Function.Injective.nontrivial (constantWeakEmbedding_injective n hn)

end MathResearch.Spinor
