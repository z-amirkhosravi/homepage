module
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Differentiation of a compactly indexed integral. The uniform bound required
by mathlib's dominated differentiation theorem follows from compactness. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology
namespace MathResearch.Analysis

variable {P K E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
  [TopologicalSpace K] [CompactSpace K] [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure K} [IsFiniteMeasure μ]

omit [NormedSpace ℝ P] [ProperSpace P] [NormedSpace ℝ E] [SecondCountableTopology K] in
/-- Every fibre of a continuous compact family is integrable. -/
theorem integrable_compact_slice {F : P → K → E} {s : Set P}
    (hF : ContinuousOn (Function.uncurry F) (s ×ˢ univ)) {x : P} (hx : x ∈ s) :
    Integrable (F x) μ := by
  have hc : Continuous (F x) := by
    apply continuousOn_univ.mp
    exact hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun a _ => ⟨hx, mem_univ a⟩)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Continuous dependence on a compact index supplies an integrable uniform bound
for the derivative on a sufficiently small closed ball in the parameter. -/
theorem hasFDerivAt_integral_compact {F : P → K → E} {F' : P → K → P →L[ℝ] E}
    {s : Set P} (hs : IsOpen s)
    (hF : ContinuousOn (Function.uncurry F) (s ×ˢ univ))
    (hF' : ContinuousOn (Function.uncurry F') (s ×ˢ univ))
    (hd : ∀ x ∈ s, ∀ a, HasFDerivAt (fun y => F y a) (F' x a) x)
    {x : P} (hx : x ∈ s) :
    HasFDerivAt (fun y => ∫ a, F y a ∂μ) (∫ a, F' x a ∂μ) x := by
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx)
  let t := Metric.closedBall x (r/2)
  have ht : t ⊆ s := fun y hy => hrs (Metric.closedBall_subset_ball (by linarith) hy)
  have hct : IsCompact (t ×ˢ (univ : Set K)) := (isCompact_closedBall x (r/2)).prod isCompact_univ
  obtain ⟨C,hC⟩ := hct.exists_bound_of_continuousOn
    (hF'.mono (Set.prod_mono ht (subset_refl _)))
  have hfc (y : P) (hy : y ∈ s) : Continuous (F y) := by
    apply continuousOn_univ.mp
    exact (hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun a _ => ⟨hy, mem_univ a⟩))
  have hfc' : Continuous (F' x) := by
    apply continuousOn_univ.mp
    exact (hF'.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun a _ => ⟨hx, mem_univ a⟩))
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (Metric.closedBall_mem_nhds x (by positivity : 0 < r/2))
  · filter_upwards [hs.mem_nhds hx] with y hy
    exact (hfc y hy).aestronglyMeasurable
  · exact (hfc x hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact hfc'.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun a y hy => hC (y,a) ⟨hy,mem_univ a⟩
  · exact integrable_const C
  · exact Filter.Eventually.of_forall fun a y hy => hd y (ht hy) a

end MathResearch.Analysis
