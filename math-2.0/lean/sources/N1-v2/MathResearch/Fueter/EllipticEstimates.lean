module

public import MathResearch.Fueter.SeriesCalculus

/-! The regularized elliptic summands and their locally summable derivative bounds. -/
@[expose] public section
noncomputable section
open scoped Quaternion Topology BigOperators ContDiff
open Filter
namespace MathResearch.Fueter

/-- Every ordered real derivative of the spatial kernel derivative `G_j`. -/
def kernelJet (j : Fin 3) (l : List (Fin 4)) : ℍ → ℍ :=
  iteratedPartial (l ++ [j.succ]) kernel

@[simp] theorem kernelJet_nil (j : Fin 3) : kernelJet j [] = kernelSpatialPartial j := rfl
@[simp] theorem kernelJet_cons (j : Fin 3) (μ : Fin 4) (l : List (Fin 4)) :
    kernelJet j (μ :: l) = coordPartial μ (kernelJet j l) := rfl

theorem kernelJet_regular (j : Fin 3) (l : List (Fin 4)) :
    TwoSidedRegularOn (kernelJet j l) punctured := kernel_iteratedPartial_regular _

theorem kernelJet_norm_le (j : Fin 3) (l : List (Fin 4)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ≠ 0, ‖kernelJet j l q‖ ≤ C * ‖q‖⁻¹ ^ (4 + l.length) := by
  simpa [kernelJet, List.length_append, List.length_cons, List.length_nil, inv_pow,
    show 3 + (l.length + 1) = 4 + l.length by omega] using
    kernel_iteratedPartial_norm_le (l ++ [j.succ])

/-- The F2 coordinate bounds also control the full real Fréchet derivative. -/
theorem kernelJet_fderiv_norm_le (j : Fin 3) (l : List (Fin 4)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ≠ 0,
      ‖fderiv ℝ (kernelJet j l) q‖ ≤ C * ‖q‖⁻¹ ^ (5 + l.length) := by
  choose C hC hb using fun μ => kernelJet_norm_le j (μ :: l)
  have hsum : 0 ≤ ∑ μ, C μ := Finset.sum_nonneg fun μ _ => hC μ
  let B : ℝ := Fintype.card (Fin 4) • ‖coordinateBasis.equivFunL.toContinuousLinearMap‖
  refine ⟨B * ∑ μ, C μ, by dsimp [B]; positivity, ?_⟩
  intro q hq
  have h := coordinateBasis.opNorm_le
    (u := fderiv ℝ (kernelJet j l) q)
    (M := (∑ μ, C μ) * ‖q‖⁻¹ ^ (5 + l.length)) (by positivity) ?_
  · simpa [B, mul_assoc] using h
  intro μ
  calc
    _ ≤ C μ * ‖q‖⁻¹ ^ (5 + l.length) := by
      simpa [kernelJet_cons, coordPartial, directional,
        show 4 + (l.length + 1) = 5 + l.length by omega] using hb μ q hq
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun ν _ => hC ν) (Finset.mem_univ μ)) (by positivity)

/-- Subtract the constant only at order zero, and only at nonzero lattice points.
This keeps each regularized bracket intact. -/
def regularizedJet (j : Fin 3) (l : List (Fin 4)) (a q : ℍ) : ℍ := by
  classical
  exact kernelJet j l (q + a) - if l = [] ∧ a ≠ 0 then kernelSpatialPartial j a else 0

@[simp] theorem regularizedJet_cons (j : Fin 3) (μ : Fin 4) (l : List (Fin 4)) (a q : ℍ) :
    regularizedJet j (μ :: l) a q = kernelJet j (μ :: l) (q + a) := by
  simp [regularizedJet]

/-- A cofinite lattice tail lies outside any fixed ball. -/
theorem lattice_eventually_norm_gt (L : Submodule ℤ ℍ) [DiscreteTopology L] (R : ℝ) :
    ∀ᶠ a : L in cofinite, R < ‖(a : ℍ)‖ := by
  let : ProperSpace L := .of_isClosed (isClosed_quaternionLattice L)
  rw [eventually_cofinite]
  simp only [not_lt]
  change {a : L | ‖a‖ ≤ R}.Finite
  simpa only [Metric.closedBall, dist_zero_right] using
    (isCompact_iff_finite.mp (isCompact_closedBall (0 : L) R))

/-- The mean value theorem gains one power of decay for the intact bracket. -/
theorem regularizedJet_zero_majorant (L : Submodule ℤ ℍ)
    [DiscreteTopology L] [IsZLattice ℝ L] (j : Fin 3)
    {K : Set ℍ} (hK : Bornology.IsBounded K) :
    ∃ u : L → ℝ, Summable u ∧
      ∀ᶠ a : L in cofinite, ∀ q ∈ K, ‖regularizedJet j [] (a : ℍ) q‖ ≤ u a := by
  obtain ⟨R, hR, hRK⟩ := hK.exists_pos_norm_le
  obtain ⟨C, hC, hb⟩ := kernelJet_fderiv_norm_le j []
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
    (𝕜 := ℝ) (f := kernelSpatialPartial j)
    (fun x hx' => ((kernelJet_regular j []).1.contDiffAt
      (isOpen_punctured.mem_nhds (hx x hx').2)).differentiableAt (by simp))
    (C := C * (‖(a : ℍ)‖ / 2)⁻¹ ^ 5)
    (fun x hx' => (by
      have hh := hb x (hx x hx').2
      simp only [kernelJet_nil, List.length_nil, Nat.add_zero] at hh
      exact hh.trans (by gcongr; exact (hx x hx').1)))
    (x := (a : ℍ)) (y := q + (a : ℍ))
    (by simp [le_of_lt hR]) (by simpa [dist_eq_norm] using hRK q hq)
  simp only [add_sub_cancel_right] at hm
  simp only [regularizedJet, kernelJet_nil, ite_eq_left (And.intro rfl hane)]
  calc
    _ ≤ (C * (‖(a : ℍ)‖ / 2)⁻¹ ^ 5) * ‖q‖ := hm
    _ ≤ (C * (‖(a : ℍ)‖ / 2)⁻¹ ^ 5) * R := by gcongr; exact hRK q hq
    _ = (C * 2 ^ 5 * R) * ‖(a : ℍ)‖⁻¹ ^ 5 := by
      rw [inv_div, div_eq_mul_inv, mul_pow]
      ring

/-- Every derivative order has a normal majorant on bounded sets. -/
theorem regularizedJet_majorant (L : Submodule ℤ ℍ)
    [DiscreteTopology L] [IsZLattice ℝ L] (j : Fin 3) (l : List (Fin 4))
    {K : Set ℍ} (hK : Bornology.IsBounded K) :
    ∃ u : L → ℝ, Summable u ∧
      ∀ᶠ a : L in cofinite, ∀ q ∈ K, ‖regularizedJet j l (a : ℍ) q‖ ≤ u a := by
  cases l with
  | nil => exact regularizedJet_zero_majorant L j hK
  | cons μ l =>
    obtain ⟨C, hC, hb⟩ := kernelJet_norm_le j (μ :: l)
    obtain ⟨u, hu, hbound⟩ := lattice_decay_majorant L (by simp) hC hb hK
    exact ⟨u, hu, by simpa only [regularizedJet_cons] using hbound⟩

/-- Any subseries has the same normal convergence property. -/
theorem regularizedJet_normal (L : Submodule ℤ ℍ)
    [DiscreteTopology L] [IsZLattice ℝ L] (j : Fin 3) (l : List (Fin 4))
    (S : Set L) (U : Set ℍ) :
    NormallySummableOn (fun a : S => regularizedJet j l (a.1 : ℍ)) U := by
  intro K _ hK
  obtain ⟨u, hu, hb⟩ := regularizedJet_majorant L j l hK.isBounded
  exact ⟨fun a => u a.1, hu.subtype _, Subtype.val_injective.tendsto_cofinite.eventually hb⟩

theorem regularizedJet_normal_all (L : Submodule ℤ ℍ)
    [DiscreteTopology L] [IsZLattice ℝ L] (j : Fin 3) (l : List (Fin 4)) (U : Set ℍ) :
    NormallySummableOn (fun a : L => regularizedJet j l (a : ℍ)) U :=
  fun _ _ hK => regularizedJet_majorant L j l hK.isBounded

end MathResearch.Fueter
