module
public import MathResearch.Spinor.CompactDensity
public import MathResearch.Spinor.RegularAction

/-! The canonical compact-support proof of strong continuity.
Change of variables gives the norm identity, so continuity of a compactly
supported matrix coefficient implies norm continuity. Density and unitarity
then extend it to the ambient L² space and its invariant regular kernel. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Quaternion Topology InnerProductSpace
open MeasureTheory Filter Set
namespace MathResearch.Spinor

theorem continuous_sp11_mul : Continuous (fun p : Sp11 × Sp11 => p.1 * p.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : Sp11 × Sp11 => (p.1 : QuaternionMatrix2) * (p.2 : QuaternionMatrix2))
  exact (continuous_sp11_coe.comp continuous_fst).mul (continuous_sp11_coe.comp continuous_snd)

/-- Continuity at the identity on the compact-support class. The dominating
function is supported on the fixed compact support of F, not the whole ball. -/
theorem continuousAt_one_weightedL2Action_compact (n : ℕ) (hn : 2 ≤ n)
    {F : ℍ → BinaryForm n} (hF : Continuous F) (hc : HasCompactSupport F)
    (hmem : MemLp F 2 (weightedBallMeasure n)) :
    ContinuousAt (fun g : Sp11 => weightedL2Action n hn g (hmem.toLp F)) 1 := by
  let f := hmem.toLp F
  obtain ⟨L, hL⟩ := hc.exists_bound_of_continuous hF
  let Fb := BoundedContinuousFunction.ofNormedAddCommGroup F hF L hL
  let a := inverseMobiusGap (1 : Sp11) / 2
  have ha : 0 < a := half_pos (inverseMobiusGap_pos 1)
  let M := a⁻¹ ^ (n+2) * ‖Fb‖
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hneigh : ∀ᶠ g in 𝓝 (1 : Sp11), a ≤ inverseMobiusGap g :=
    continuous_inverseMobiusGap.continuousAt.eventually
      (le_mem_nhds (half_lt_self (inverseMobiusGap_pos 1)))
  let D : Sp11 → ℍ → ℂ := fun g q => inner ℂ (ballRepresentation n g F q) (F q)
  let bound : ℍ → ℝ := (tsupport F).indicator (fun _ => M * ‖Fb‖)
  have hmeas (g : Sp11) : AEStronglyMeasurable (D g) (weightedBallMeasure n) :=
    (ballAction_aestronglyMeasurable n hn (isSp11_signatureAdjoint g.property)
      hF.aestronglyMeasurable).inner hF.aestronglyMeasurable
  have hbound : ∀ᶠ g in 𝓝 (1 : Sp11), ∀ᵐ q ∂weightedBallMeasure n, ‖D g q‖ ≤ bound q := by
    filter_upwards [hneigh] with g hg
    filter_upwards [ae_mem_ball n hn] with q hq
    by_cases hs : q ∈ tsupport F
    · rw [show bound q = M * ‖Fb‖ from indicator_of_mem hs _]
      exact (norm_inner_le_norm _ _).trans (mul_le_mul
        (ballRepresentation_bound n g Fb ha hg hq) (Fb.norm_coe_le_norm q) (norm_nonneg _) hM)
    · have hz : F q = 0 := image_eq_zero_of_notMem_tsupport hs
      simp [D, bound, hs, hz]
  have hbint : Integrable bound (weightedBallMeasure n) :=
    (integrable_indicator_iff hc.measurableSet).mpr (integrableOn_const hc.measure_lt_top.ne)
  have hpoint : ∀ᵐ q ∂weightedBallMeasure n,
      Tendsto (fun g => D g q) (𝓝 (1 : Sp11)) (𝓝 (inner ℂ (F q) (F q))) := by
    filter_upwards [ae_mem_ball n hn] with q hq
    simpa only [D, Sp11.coe_one, ballRepresentation_one] using
      ((continuousAt_ballRepresentation_parameter n hF 1 hq).tendsto.inner (𝕜 := ℂ) (tendsto_const_nhds (x := F q)))
  have hdct := tendsto_integral_filter_of_dominated_convergence bound
    (Eventually.of_forall hmeas) hbound hbint hpoint
  have he (g : Sp11) : inner ℂ (weightedL2Action n hn g f) f = ∫ q, D g q ∂weightedBallMeasure n := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [weightedL2Action_ae_of_representative n hn g f F hmem.coeFn_toLp,
      hmem.coeFn_toLp] with q hg hf
    rw [hg, hf]
  have hself : inner ℂ f f = ∫ q, inner ℂ (F q) (F q) ∂weightedBallMeasure n := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hmem.coeFn_toLp] with q hq
    rw [hq]
  have hi : Tendsto (fun g => inner ℂ (weightedL2Action n hn g f) f)
      (𝓝 (1 : Sp11)) (𝓝 (inner ℂ f f)) := by simpa only [he, hself] using hdct
  have hre : Tendsto (fun g => RCLike.re (inner ℂ (weightedL2Action n hn g f) f))
      (𝓝 (1 : Sp11)) (𝓝 (‖f‖^2)) := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) f]
    exact Complex.continuous_re.continuousAt.tendsto.comp hi
  have hsq : Tendsto (fun g => ‖weightedL2Action n hn g f - f‖^2) (𝓝 (1 : Sp11)) (𝓝 (0 : ℝ)) := by
    have h := ((tendsto_const_nhds (x := ‖f‖^2)).sub
      ((tendsto_const_nhds (x := (2:ℝ))).mul hre)).add (tendsto_const_nhds (x := ‖f‖^2))
    simpa only [Function.comp_def, norm_sub_sq (𝕜 := ℂ), weightedL2Action_norm,
      show ‖f‖^2 - 2 * ‖f‖^2 + ‖f‖^2 = 0 by ring] using h
  rw [ContinuousAt, weightedL2Action_one]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hsq

theorem continuous_weightedL2Action_compact (n : ℕ) (hn : 2 ≤ n)
    {F : ℍ → BinaryForm n} (hF : Continuous F) (hc : HasCompactSupport F)
    (hmem : MemLp F 2 (weightedBallMeasure n)) :
    Continuous (fun g : Sp11 => weightedL2Action n hn g (hmem.toLp F)) := by
  apply continuous_iff_continuousAt.mpr
  intro g
  have hm : Continuous (fun h : Sp11 => g⁻¹ * h) :=
    continuous_sp11_mul.comp (continuous_const.prodMk continuous_id)
  have ht := (continuousAt_one_weightedL2Action_compact n hn hF hc hmem).tendsto.comp
    (by simpa only [inv_mul_cancel] using hm.tendsto g)
  have hu := (weightedL2Unitary n hn g).continuous.continuousAt.tendsto.comp ht
  change Tendsto (fun h => weightedL2Action n hn g (weightedL2Action n hn (g⁻¹*h) (hmem.toLp F)))
    (𝓝 g) (𝓝 (weightedL2Action n hn g (weightedL2Action n hn 1 (hmem.toLp F)))) at hu
  simpa only [ContinuousAt, weightedL2Action_one, ← weightedL2Action_mul, mul_inv_cancel_left] using hu

/-- The dense-class extension uses exactly compactly supported continuous functions in B. -/
theorem continuous_weightedL2Representation_by_compact (n : ℕ) (hn : 2 ≤ n) :
    Continuous (fun z : BallL2 n × Sp11 => weightedL2Representation n hn z.2 z.1) := by
  change Continuous (fun z : BallL2 n × Sp11 => weightedL2Action n hn z.2 z.1)
  apply continuous_prod_of_dense_continuous_lipschitzWith _ 1 (dense_compactContinuousBallClasses n hn)
  · rintro f ⟨F, hF, hc, _hs, hmem, rfl⟩
    exact continuous_weightedL2Action_compact n hn hF hc hmem
  · intro g
    exact (weightedL2Unitary n hn g).isometry.lipschitzWith

theorem stronglyContinuous_regularRepresentation_by_compact (n : ℕ) (hn : 2 ≤ n)
    (f : WeakBallSpace n hn) : Continuous (fun g : Sp11 => regularRepresentation n hn g f) := by
  apply Continuous.subtype_mk
  have h := (continuous_weightedL2Representation_by_compact n hn).comp
    (continuous_const.prodMk continuous_id : Continuous (fun g : Sp11 => (f.val, g)))
  exact h

end MathResearch.Spinor
