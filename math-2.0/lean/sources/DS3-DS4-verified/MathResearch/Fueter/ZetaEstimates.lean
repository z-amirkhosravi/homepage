module
public import MathResearch.Fueter.ZetaSummands
@[expose] public section
noncomputable section
open scoped Quaternion Topology BigOperators ContDiff
open Filter
namespace MathResearch.Fueter

/-- The first derivative of the Taylor remainder gains one power of decay. -/
theorem zetaJet_one_majorant (L : Submodule ℤ ℍ)
    [DiscreteTopology L] [IsZLattice ℝ L] (μ : Fin 4)
    {K : Set ℍ} (hK : Bornology.IsBounded K) :
    ∃ u : L → ℝ, Summable u ∧
      ∀ᶠ a : L in cofinite, ∀ q ∈ K, ‖zetaJet [μ] (a : ℍ) q‖ ≤ u a := by
  obtain ⟨R, hR, hRK⟩ := hK.exists_pos_norm_le
  obtain ⟨C, hC, hb⟩ := kernel_iteratedPartial_fderiv_norm_le [μ]
  refine ⟨fun a => (C * 2 ^ 5 * R) * ‖(a : ℍ)‖⁻¹ ^ 5,
    (summable_lattice_inv_pow L 5 (by omega)).mul_left _, ?_⟩
  filter_upwards [lattice_eventually_norm_gt L (2 * R + 1)] with a ha
  intro q hq
  have hapos : 0 < ‖(a : ℍ)‖ := by linarith
  have hane : (a : ℍ) ≠ 0 := norm_pos_iff.mp hapos
  have hx (x : ℍ) (hx : x ∈ Metric.closedBall (a : ℍ) R) :
      ‖(a : ℍ)‖ / 2 ≤ ‖x‖ ∧ x ≠ 0 := by
    have hxR : ‖x - (a : ℍ)‖ ≤ R := by simpa [dist_eq_norm] using hx
    have ht := norm_sub_norm_le (a : ℍ) x
    rw [norm_sub_rev] at ht
    constructor
    · linarith
    · apply norm_pos_iff.mp; linarith
  have hm := (convex_closedBall (a : ℍ) R).norm_image_sub_le_of_norm_fderiv_le
    (𝕜 := ℝ) (f := coordPartial μ kernel)
    (fun x hx' => ((kernel_iteratedPartial_regular [μ]).1.contDiffAt
      (isOpen_punctured.mem_nhds (hx x hx').2)).differentiableAt (by simp))
    (C := C * (‖(a : ℍ)‖ / 2)⁻¹ ^ 5)
    (fun x hx' => (by
      have hh := hb x (hx x hx').2
      simp only [iteratedPartial, List.length_cons, List.length_nil, Nat.reduceAdd] at hh
      exact hh.trans (by gcongr; exact (hx x hx').1)))
    (x := (a : ℍ)) (y := q + (a : ℍ))
    (by simp [le_of_lt hR]) (by simpa [dist_eq_norm] using hRK q hq)
  simp only [add_sub_cancel_right] at hm
  simp only [zetaJet, ite_eq_right hane, iteratedPartial]
  calc
    _ ≤ (C * (‖(a : ℍ)‖ / 2)⁻¹ ^ 5) * ‖q‖ := hm
    _ ≤ (C * (‖(a : ℍ)‖ / 2)⁻¹ ^ 5) * R := by gcongr; exact hRK q hq
    _ = (C * 2 ^ 5 * R) * ‖(a : ℍ)‖⁻¹ ^ 5 := by
      rw [inv_div, div_eq_mul_inv, mul_pow]
      ring


/-- A second application of the mean value theorem controls the intact E-C2 bracket. -/
theorem zetaJet_zero_majorant (L : Submodule ℤ ℍ)
    [DiscreteTopology L] [IsZLattice ℝ L]
    {K : Set ℍ} (hK : Bornology.IsBounded K) :
    ∃ u : L → ℝ, Summable u ∧
      ∀ᶠ a : L in cofinite, ∀ q ∈ K, ‖zetaJet [] (a : ℍ) q‖ ≤ u a := by
  obtain ⟨R, hR, hRK⟩ := hK.exists_pos_norm_le
  choose u hu hb using fun μ => zetaJet_one_majorant L μ (Metric.isBounded_closedBall (x := (0 : ℍ)) (r := R))
  let B : ℝ := Fintype.card (Fin 4) • ‖coordinateBasis.equivFunL.toContinuousLinearMap‖
  let M : L → ℝ := fun a => B * ∑ μ, |u μ a|
  have hM (a : L) : 0 ≤ M a := by dsimp [M, B]; positivity
  refine ⟨fun a => M a * R, ((summable_sum (fun μ _ => (hu μ).abs)).mul_left B).mul_right R, ?_⟩
  have hall : ∀ᶠ a : L in cofinite, ∀ μ, ∀ q ∈ Metric.closedBall (0 : ℍ) R,
      ‖zetaJet [μ] (a : ℍ) q‖ ≤ u μ a := Filter.eventually_all.mpr hb
  filter_upwards [hall, lattice_eventually_norm_gt L (R + 1)] with a ha hn
  have hane : (a : ℍ) ≠ 0 := norm_pos_iff.mp (by linarith)
  have hx (x : ℍ) (hx : x ∈ Metric.closedBall (0 : ℍ) R) : x + (a : ℍ) ≠ 0 := by
    have hxn : ‖x‖ ≤ R := by simpa using hx
    intro hz
    have he : (a : ℍ) = -x := eq_neg_of_add_eq_zero_right hz
    rw [he, norm_neg] at hn
    linarith
  have hd (x : ℍ) (hx' : x ∈ Metric.closedBall (0 : ℍ) R) :
      ‖fderiv ℝ (zetaJet [] (a : ℍ)) x‖ ≤ M a := by
    apply coordinateBasis.opNorm_le (by positivity)
    intro μ
    change ‖coordPartial μ (zetaJet [] (a : ℍ)) x‖ ≤ _
    rw [zetaJet_partial [] μ _ x (hx x hx')]
    exact (ha μ x hx').trans ((le_abs_self _).trans
      (Finset.single_le_sum (fun ν _ => abs_nonneg (u ν a)) (Finset.mem_univ μ)))
  intro q hq
  have hm := (convex_closedBall (0 : ℍ) R).norm_image_sub_le_of_norm_fderiv_le
    (𝕜 := ℝ) (f := zetaJet [] (a : ℍ))
    (fun x hx' => (zetaJet_hasFDerivAt [] _ x (hx x hx')).differentiableAt)
    (C := M a) hd (x := 0) (y := q) (by simp [le_of_lt hR])
    (by simpa using hRK q hq)
  have hz : zetaJet [] (a : ℍ) 0 = 0 := by simp [zetaJet, hane, iteratedPartial]
  simpa [hz] using hm.trans (mul_le_mul_of_nonneg_left (by simpa using hRK q hq) (hM a))

/-- All ordered real partial derivatives admit summable majorants on bounded sets. -/
theorem zetaJet_majorant (L : Submodule ℤ ℍ)
    [DiscreteTopology L] [IsZLattice ℝ L] (l : List (Fin 4))
    {K : Set ℍ} (hK : Bornology.IsBounded K) :
    ∃ u : L → ℝ, Summable u ∧
      ∀ᶠ a : L in cofinite, ∀ q ∈ K, ‖zetaJet l (a : ℍ) q‖ ≤ u a := by
  cases l with
  | nil => exact zetaJet_zero_majorant L hK
  | cons μ l =>
    cases l with
    | nil => exact zetaJet_one_majorant L μ hK
    | cons ν l =>
      obtain ⟨C, hC, hb⟩ := kernel_iteratedPartial_norm_le (μ :: ν :: l)
      have hb' (q : ℍ) (hq : q ≠ 0) :
          ‖iteratedPartial (μ :: ν :: l) kernel q‖ ≤ C * ‖q‖⁻¹ ^ (3 + (μ :: ν :: l).length) := by
        simpa only [inv_pow] using hb q hq
      obtain ⟨u, hu, hbound⟩ := lattice_decay_majorant L (by simp; omega) hC hb' hK
      exact ⟨u, hu, by simpa only [zetaJet_cons_cons] using hbound⟩

theorem zetaJet_normal_all (L : Submodule ℤ ℍ)
    [DiscreteTopology L] [IsZLattice ℝ L] (l : List (Fin 4)) (U : Set ℍ) :
    NormallySummableOn (fun a : L => zetaJet l (a : ℍ)) U :=
  fun _ _ hK => zetaJet_majorant L l hK.isBounded

theorem zetaJet_normal (L : Submodule ℤ ℍ)
    [DiscreteTopology L] [IsZLattice ℝ L] (l : List (Fin 4)) (S : Set L) (U : Set ℍ) :
    NormallySummableOn (fun a : S => zetaJet l (a.1 : ℍ)) U := by
  intro K _ hK
  obtain ⟨u, hu, hb⟩ := zetaJet_majorant L l hK.isBounded
  exact ⟨fun a => u a.1, hu.subtype _, Subtype.val_injective.tendsto_cofinite.eventually hb⟩

end MathResearch.Fueter
