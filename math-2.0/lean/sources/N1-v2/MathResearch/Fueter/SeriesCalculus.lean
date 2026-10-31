module

public import MathResearch.Fueter.LatticeSums
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! Local normal convergence and differentiation in all four real coordinates. -/
@[expose] public section
noncomputable section
open scoped Quaternion Topology BigOperators ContDiff
open Filter
namespace MathResearch.Fueter

/-- A summable bound on every compact set, allowing finitely many exceptional terms. -/
def NormallySummableOn {ι E : Type*} [NormedAddCommGroup E]
    (f : ι → ℍ → E) (U : Set ℍ) : Prop :=
  ∀ K : Set ℍ, K ⊆ U → IsCompact K → ∃ u : ι → ℝ, Summable u ∧
    ∀ᶠ i in cofinite, ∀ q ∈ K, ‖f i q‖ ≤ u i

theorem NormallySummableOn.summable_norm {ι E : Type*} [NormedAddCommGroup E]
    {f : ι → ℍ → E} {U : Set ℍ} (h : NormallySummableOn f U) {q : ℍ} (hq : q ∈ U) :
    Summable (fun i => ‖f i q‖) := by
  obtain ⟨u, hu, hb⟩ := h {q} (Set.singleton_subset_iff.mpr hq) (isCompact_singleton)
  apply Summable.of_norm_bounded_eventually hu
  filter_upwards [hb] with i hi
  simpa using hi q (Set.mem_singleton q)

theorem NormallySummableOn.hasSumLocallyUniformlyOn {ι E : Type*}
    [NormedAddCommGroup E] [CompleteSpace E] {f : ι → ℍ → E} {U : Set ℍ}
    (h : NormallySummableOn f U) (hU : IsOpen U) :
    HasSumLocallyUniformlyOn f (fun q => ∑' i, f i q) U := by
  apply hasSumLocallyUniformlyOn_of_forall_compact hU
  intro K hKU hK
  obtain ⟨u, hu, hb⟩ := h K hKU hK
  exact hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr
    (tendstoUniformlyOn_tsum_of_cofinite_eventually hu hb)

/-- Control of the derivative in operator norm by four coordinate derivatives. -/
theorem normal_fderiv {ι : Type*} {f : ι → ℍ → ℍ} {U : Set ℍ}
    (h : ∀ μ, NormallySummableOn (fun i => coordPartial μ (f i)) U) :
    NormallySummableOn (fun i => fderiv ℝ (f i)) U := by
  intro K hKU hK
  choose u hu hb using fun μ => h μ K hKU hK
  let C : ℝ := Fintype.card (Fin 4) • ‖coordinateBasis.equivFunL.toContinuousLinearMap‖
  refine ⟨fun i => C * ∑ μ, |u μ i|,
    (summable_sum (fun μ _ => (hu μ).abs)).mul_left C, ?_⟩
  have hall : ∀ᶠ i in cofinite, ∀ μ, ∀ q ∈ K, ‖coordPartial μ (f i) q‖ ≤ u μ i :=
    Filter.eventually_all.mpr hb
  filter_upwards [hall] with i hi
  intro q hq
  apply coordinateBasis.opNorm_le (by positivity)
  intro μ
  exact (hi μ q hq).trans ((le_abs_self _).trans
    (Finset.single_le_sum (fun ν _ => abs_nonneg (u ν i)) (Finset.mem_univ μ)))

/-- Differentiation of a locally normally convergent series. -/
theorem hasFDerivAt_tsum_of_normal {ι : Type*} {f : ι → ℍ → ℍ} {U : Set ℍ}
    (hU : IsOpen U) (hf : ∀ i, DifferentiableOn ℝ (f i) U)
    (h0 : NormallySummableOn f U)
    (h1 : NormallySummableOn (fun i => fderiv ℝ (f i)) U)
    {q : ℍ} (hq : q ∈ U) :
    HasFDerivAt (fun x => ∑' i, f i x) (∑' i, fderiv ℝ (f i) q) q := by
  classical
  apply hasFDerivAt_of_tendstoLocallyUniformlyOn hU
    (h1.hasSumLocallyUniformlyOn hU)
  · intro s x hx
    exact HasFDerivAt.fun_sum fun i _ =>
      ((hf i x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  · intro x hx
    exact (h0.summable_norm hx).of_norm.hasSum
  · exact hq

/-- A smooth family of jets with normally convergent coordinate derivatives has a smooth sum.
The list indices include time derivatives and every order, not just spatial derivatives. -/
theorem contDiffOn_tsum_of_jets {ι : Type*}
    (f : List (Fin 4) → ι → ℍ → ℍ) {U : Set ℍ} (hU : IsOpen U)
    (hd : ∀ l i, DifferentiableOn ℝ (f l i) U)
    (hp : ∀ l μ i q, q ∈ U → coordPartial μ (f l i) q = f (μ :: l) i q)
    (hn : ∀ l, NormallySummableOn (f l) U) :
    (∀ l, ContDiffOn ℝ ∞ (fun q => ∑' i, f l i q) U) ∧
    (∀ l μ q, q ∈ U →
      coordPartial μ (fun x => ∑' i, f l i x) q = ∑' i, f (μ :: l) i q) := by
  have hn' (l) : NormallySummableOn (fun i => fderiv ℝ (f l i)) U := by
    apply normal_fderiv
    intro μ K hKU hK
    obtain ⟨u, hu, hb⟩ := hn (μ :: l) K hKU hK
    refine ⟨u, hu, ?_⟩
    filter_upwards [hb] with i hi
    intro q hq
    rw [hp l μ i q (hKU hq)]
    exact hi q hq
  have hd' (l) (q) (hq : q ∈ U) :=
    hasFDerivAt_tsum_of_normal hU (hd l) (hn l) (hn' l) hq
  have hp' (l) (μ) (q) (hq : q ∈ U) :
      coordPartial μ (fun x => ∑' i, f l i x) q = ∑' i, f (μ :: l) i q := by
    unfold coordPartial directional
    rw [(hd' l q hq).fderiv]
    calc
      _ = ∑' i, fderiv ℝ (f l i) q (coordinateBasis μ) := by
        exact (ContinuousLinearMap.apply ℝ ℍ (coordinateBasis μ)).map_tsum
          ((hn' l).summable_norm hq).of_norm
      _ = _ := ?_
    apply tsum_congr
    intro i
    exact hp l μ i q hq
  refine ⟨?_, hp'⟩
  have hs : ∀ n : ℕ, ∀ l, ContDiffOn ℝ n (fun q => ∑' i, f l i q) U := by
    intro n
    induction n with
    | zero =>
      intro l
      exact contDiffOn_zero.mpr (fun q hq => (hd' l q hq).continuousAt.continuousWithinAt)
    | succ n ih =>
      intro l
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨fun q hq => (hd' l q hq).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      apply contDiffOn_clm_apply.mpr
      intro v
      have hsum := ContDiffOn.sum (s := Finset.univ)
        (fun μ _ => (ih (μ :: l)).const_smul (coordinateBasis.repr v μ))
      apply hsum.congr
      intro q hq
      conv_lhs => rw [← coordinateBasis.sum_repr v, map_sum]; simp only [map_smul]
      apply Finset.sum_congr rfl
      intro μ _
      congr 1
      exact hp' l μ q hq
  intro l
  exact contDiffOn_infty.mpr fun n => hs n l

end MathResearch.Fueter
