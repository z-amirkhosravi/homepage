module
public import MathResearch.Spinor.WeightedL2Action
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-! Strong continuity of the concrete ambient C7 action.
This uses bounded continuous approximation and finite weighted mass. It is an
alternative to the compact-support approximation in R060 section 3; that
proof difference is recorded in the internal continuation notes. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Quaternion ENNReal Topology BoundedContinuousFunction Matrix.Norms.Elementwise
open MeasureTheory Filter
namespace MathResearch.Spinor

theorem continuous_signatureAdjoint : Continuous signatureAdjoint := by
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  fin_cases i <;> fin_cases j <;> simp only [signatureAdjoint] <;> fun_prop

theorem continuous_sp11_coe : Continuous (fun g : Sp11 => (g : QuaternionMatrix2)) :=
  continuous_subtype_val

instance sp11FirstCountableTopology : FirstCountableTopology Sp11 :=
  inferInstanceAs (FirstCountableTopology {g : QuaternionMatrix2 // IsSp11 g})

theorem IsSp11.row_norms {g : QuaternionMatrix2} (hg : IsSp11 g) :
    Quaternion.normSq (g 1 1) - Quaternion.normSq (g 1 0) = 1 := by
  have h := congrArg (fun M : QuaternionMatrix2 => (M 1 1).re) hg.2
  simpa [signatureAdjoint, Matrix.mul_apply, Fin.sum_univ_two,
    Quaternion.normSq_def', pow_two, sub_eq_add_neg, mul_comm, add_comm] using h

def inverseMobiusGap (g : Sp11) : ℝ :=
  ‖(signatureAdjoint g) 1 1‖ - ‖(signatureAdjoint g) 1 0‖

theorem inverseMobiusGap_pos (g : Sp11) : 0 < inverseMobiusGap g := by
  have h := (isSp11_signatureAdjoint g.property).row_norms
  rw [Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_eq_norm_mul_self] at h
  unfold inverseMobiusGap
  nlinarith [norm_nonneg ((signatureAdjoint g) 1 0), norm_nonneg ((signatureAdjoint g) 1 1)]

theorem continuous_inverseMobiusGap : Continuous inverseMobiusGap := by
  have h := continuous_signatureAdjoint.comp continuous_sp11_coe
  exact ((continuous_apply 1).comp ((continuous_apply 1).comp h)).norm.sub
    ((continuous_apply 0).comp ((continuous_apply 1).comp h)).norm

theorem inverseMobiusGap_le_norm (g : Sp11) {q : ℍ} (hq : q ∈ Ball) :
    inverseMobiusGap g ≤ ‖mobiusDenominator (signatureAdjoint g) q‖ := by
  have hq' : ‖q‖ ≤ 1 := ((mem_ball_iff q).mp hq).le
  have h := norm_sub_le ((signatureAdjoint g) 1 0 * q + (signatureAdjoint g) 1 1)
    ((signatureAdjoint g) 1 0 * q)
  simp only [add_sub_cancel_left, norm_mul] at h
  have hc := mul_le_mul_of_nonneg_left hq' (norm_nonneg ((signatureAdjoint g) 1 0))
  dsimp only [inverseMobiusGap, mobiusDenominator]
  nlinarith

theorem ballRepresentation_bound (n : ℕ) (g : Sp11) (F : ℍ →ᵇ BinaryForm n)
    {a : ℝ} (ha : 0 < a) (hag : a ≤ inverseMobiusGap g) {q : ℍ} (hq : q ∈ Ball) :
    ‖ballRepresentation n g F q‖ ≤ a⁻¹ ^ (n+2) * ‖F‖ := by
  rw [ballRepresentation, ballAction_norm]
  apply mul_le_mul
  · exact pow_le_pow_left₀ (by positivity)
      (inv_le_inv₀ (lt_of_lt_of_le ha (hag.trans (inverseMobiusGap_le_norm g hq))) ha |>.mpr
        (hag.trans (inverseMobiusGap_le_norm g hq))) _
  · exact F.norm_coe_le_norm _
  · exact norm_nonneg _
  · positivity

theorem continuousAt_ballRepresentation_parameter (n : ℕ) {F : ℍ → BinaryForm n}
    (hF : Continuous F) (g : Sp11) {q : ℍ} (hq : q ∈ Ball) :
    ContinuousAt (fun h : Sp11 => ballRepresentation n h F q) g := by
  have hmat := continuous_signatureAdjoint.comp continuous_sp11_coe
  have hentry (i j : Fin 2) : Continuous (fun h : Sp11 => (signatureAdjoint h) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp hmat)
  have hJ : Continuous (fun h : Sp11 => mobiusDenominator (signatureAdjoint h) q) :=
    ((hentry 1 0).mul continuous_const).add (hentry 1 1)
  have hne := mobiusDenominator_ne_zero (isSp11_signatureAdjoint g.property) hq
  have hi := hJ.continuousAt.inv₀ hne
  have hp : ContinuousAt (fun h : Sp11 => mobiusPoint (signatureAdjoint h) q) g :=
    (((hentry 0 0).mul continuous_const).add (hentry 0 1)).continuousAt.mul hi
  have hv := (contDiff_quaternionPolynomialRepresentation n).continuous.continuousAt.comp
    (hi.prodMk (hF.continuousAt.comp hp))
  have hw := (Quaternion.continuous_normSq.comp hJ).continuousAt.inv₀
    (Quaternion.normSq_ne_zero.mpr hne)
  exact hw.smul hv

theorem weightedL2Action_ae_of_representative (n : ℕ) (hn : 2 ≤ n) (g : Sp11)
    (f : BallL2 n) (F : ℍ → BinaryForm n) (hF : (f : ℍ → BinaryForm n) =ᵐ[weightedBallMeasure n] F) :
    (weightedL2Action n hn g f : ℍ → BinaryForm n) =ᵐ[weightedBallMeasure n]
      ballRepresentation n g F := by
  have hcomp := (mobius_quasiMeasurePreserving_weighted n hn
    (isSp11_signatureAdjoint g.property)).ae hF
  filter_upwards [weightedL2Action_ae n hn g f, hcomp] with q hq hc
  rw [hq]
  simp only [ballRepresentation, ballAction, hc]

/-- Continuity on the bounded continuous dense class, by dominated convergence
with an explicit local bound on the nonconstant fibre multiplier. -/
theorem continuous_weightedL2Action_boundedContinuous (n : ℕ) (hn : 2 ≤ n)
    (F : ℍ →ᵇ BinaryForm n) : Continuous (fun g : Sp11 => weightedL2Action n hn g
      (BoundedContinuousFunction.toLp 2 (weightedBallMeasure n) ℂ F)) := by
  let f := BoundedContinuousFunction.toLp 2 (weightedBallMeasure n) ℂ F
  have hrep := BoundedContinuousFunction.coeFn_toLp 2 (weightedBallMeasure n) ℂ F
  have ha (g : Sp11) := weightedL2Action_ae_of_representative n hn g f F hrep
  have hB : ∀ᵐ q ∂weightedBallMeasure n, q ∈ Ball :=
    (ae_weightedBall_iff n hn _).mpr (ae_restrict_mem ball_isOpen.measurableSet)
  apply continuous_iff_continuousAt.mpr
  intro g
  let a := inverseMobiusGap g / 2
  have ha_pos : 0 < a := half_pos (inverseMobiusGap_pos g)
  have hag : a ≤ inverseMobiusGap g := half_le_self (inverseMobiusGap_pos g).le
  let M := a⁻¹ ^ (n+2) * ‖F‖
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hneigh : ∀ᶠ h in 𝓝 g, a ≤ inverseMobiusGap h := by
    apply (continuous_inverseMobiusGap.continuousAt.eventually (le_mem_nhds ?_))
    exact half_lt_self (inverseMobiusGap_pos g)
  let D : Sp11 → ℍ → ℝ := fun h q => ‖ballRepresentation n h F q - ballRepresentation n g F q‖^2
  have hmeas (h : Sp11) : AEStronglyMeasurable (D h) (weightedBallMeasure n) := by
    have hm := ((ballAction_aestronglyMeasurable n hn (isSp11_signatureAdjoint h.property)
      F.continuous.aestronglyMeasurable).sub
      (ballAction_aestronglyMeasurable n hn (isSp11_signatureAdjoint g.property)
        F.continuous.aestronglyMeasurable)).norm
    convert! (continuous_pow 2).comp_aestronglyMeasurable hm using 1
  have hbound : ∀ᶠ h in 𝓝 g, ∀ᵐ q ∂weightedBallMeasure n, ‖D h q‖ ≤ (2*M)^2 := by
    filter_upwards [hneigh] with h hh
    filter_upwards [hB] with q hq
    have hhq := ballRepresentation_bound n h F ha_pos hh hq
    have hgq := ballRepresentation_bound n g F ha_pos hag hq
    have hd := norm_sub_le (ballRepresentation n h F q) (ballRepresentation n g F q)
    dsimp only [D]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (by dsimp only [M] at *; linarith) 2
  have hpoint : ∀ᵐ q ∂weightedBallMeasure n, Tendsto (fun h => D h q) (𝓝 g) (𝓝 (0 : ℝ)) := by
    filter_upwards [hB] with q hq
    have h := ((continuousAt_ballRepresentation_parameter n F.continuous g hq).tendsto.sub
      (tendsto_const_nhds (x := ballRepresentation n g F q))).norm.pow 2
    simpa [D] using h
  have hdct := tendsto_integral_filter_of_dominated_convergence (fun _ : ℍ => (2*M)^2)
    (Eventually.of_forall hmeas) hbound (integrable_const _) hpoint
  have he (h : Sp11) : ‖weightedL2Action n hn h f - weightedL2Action n hn g f‖^2 =
      ∫ q, D h q ∂weightedBallMeasure n := by
    rw [l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (weightedL2Action n hn h f) (weightedL2Action n hn g f),
      ha h, ha g] with q hsub hh hg
    dsimp only [D]
    rw [hsub]
    simp only [Pi.sub_apply, hh, hg]
  have hsq : Tendsto (fun h => ‖weightedL2Action n hn h f - weightedL2Action n hn g f‖^2)
      (𝓝 g) (𝓝 (0 : ℝ)) := by
    simpa only [he, integral_zero] using hdct
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt

/-- The ambient representation is strongly continuous. The proof uses the
bounded-continuous alternative recorded in the internal notes, not an assumed
continuity property or the unproved regularity of the kernel. -/
theorem continuous_weightedL2Representation (n : ℕ) (hn : 2 ≤ n) :
    Continuous (fun z : BallL2 n × Sp11 => weightedL2Representation n hn z.2 z.1) := by
  change Continuous (fun z : BallL2 n × Sp11 => weightedL2Action n hn z.2 z.1)
  apply continuous_prod_of_dense_continuous_lipschitzWith _ 1
    (BoundedContinuousFunction.toLp_denseRange (BinaryForm n) (weightedBallMeasure n) ℂ
      (p := 2) (by norm_num))
  · intro f hf
    obtain ⟨F, rfl⟩ := hf
    exact continuous_weightedL2Action_boundedContinuous n hn F
  · intro g
    exact (weightedL2Unitary n hn g).isometry.lipschitzWith

theorem stronglyContinuous_weightedL2Representation (n : ℕ) (hn : 2 ≤ n) (f : BallL2 n) :
    Continuous (fun g : Sp11 => weightedL2Representation n hn g f) := by
  have h : Continuous (fun g : Sp11 => (f, g)) := continuous_const.prodMk continuous_id
  change Continuous (fun g : Sp11 => weightedL2Action n hn g f)
  have hc : Continuous (fun z : BallL2 n × Sp11 => weightedL2Action n hn z.2 z.1) :=
    continuous_weightedL2Representation n hn
  simpa only [Function.comp_def] using! hc.comp h

end MathResearch.Spinor
