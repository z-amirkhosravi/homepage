module

public import MathResearch.Fueter.Elliptic
public import Mathlib.Analysis.Normed.Module.Connected

/-! E2: evenness and periodicity of the regularized quaternionic elliptic functions. -/
@[expose] public section
noncomputable section
open scoped Quaternion Topology BigOperators ContDiff
namespace MathResearch.Fueter

theorem kernelSpatialPartial_even_all (j : Fin 3) (q : ℍ) :
    kernelSpatialPartial j (-q) = kernelSpatialPartial j q := by
  by_cases hq : q = 0
  · simp [hq]
  · exact kernelSpatialPartial_even j q hq

/-- Evenness reindexes intact brackets; it does not split a borderline divergent sum. -/
theorem elliptic_even (L : Submodule ℤ ℍ) (j : Fin 3) (q : ℍ) :
    elliptic L j (-q) = elliptic L j q := by
  unfold elliptic
  rw [kernelSpatialPartial_even_all]
  congr 1
  rw [← (nonzeroLatticeNeg L).tsum_eq]
  apply tsum_congr
  intro a
  change kernelSpatialPartial j (-q + -(a.1 : ℍ)) - kernelSpatialPartial j (-(a.1 : ℍ)) = _
  rw [← neg_add, kernelSpatialPartial_even_all, kernelSpatialPartial_even_all]

theorem not_mem_lattice_add (L : Submodule ℤ ℍ) (w : L) {q : ℍ} (hq : q ∉ L) :
    q + (w : ℍ) ∉ L := by
  intro h
  exact hq (by simpa using L.sub_mem h w.2)

variable (L : Submodule ℤ ℍ) [DiscreteTopology L] [IsZLattice ℝ L]

/-- E1 identifies every first real derivative with a genuinely convergent full lattice sum. -/
theorem elliptic_coordPartial (j : Fin 3) (μ : Fin 4) {q : ℍ} (hq : q ∉ L) :
    coordPartial μ (elliptic L j) q = ∑' a : L, kernelJet j [μ] (q + (a : ℍ)) := by
  simpa only [iteratedPartial, regularizedJet_cons] using elliptic_iteratedPartial L j [μ] hq

theorem elliptic_coordPartial_add (j : Fin 3) (μ : Fin 4) (w : L) {q : ℍ} (hq : q ∉ L) :
    coordPartial μ (elliptic L j) (q + (w : ℍ)) = coordPartial μ (elliptic L j) q := by
  rw [elliptic_coordPartial L j μ (not_mem_lattice_add L w hq), elliptic_coordPartial L j μ hq]
  simpa [add_assoc] using (Equiv.addLeft w).tsum_eq
    (fun a : L => kernelJet j [μ] (q + (a : ℍ)))

theorem elliptic_fderiv_add (j : Fin 3) (w : L) {q : ℍ} (hq : q ∉ L) :
    fderiv ℝ (elliptic L j) (q + (w : ℍ)) = fderiv ℝ (elliptic L j) q := by
  apply ContinuousLinearMap.ext
  intro v
  rw [← coordinateBasis.sum_repr v]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro μ _
  congr 1
  exact elliptic_coordPartial_add L j μ w hq

omit [IsZLattice ℝ L] in
/-- Mathlib supplies path connectedness of the complement of a countable set in real
 dimension greater than one. A discrete quaternionic lattice satisfies these hypotheses. -/
theorem isConnected_lattice_compl : IsConnected (L : Set ℍ)ᶜ := by
  have hc : (L : Set ℍ).Countable := (isClosed_quaternionLattice L).isLindelof.countable inferInstance
  apply hc.isConnected_compl_of_one_lt_rank
  rw [← Module.finrank_eq_rank, Quaternion.finrank_eq_four]
  norm_num

/-- Vanishing derivatives make the period increment constant on the entire domain;
evenness makes that constant its own negative, hence zero. -/
theorem elliptic_add (j : Fin 3) (w : L) {q : ℍ} (hq : q ∉ L) :
    elliptic L j (q + (w : ℍ)) = elliptic L j q := by
  let H : ℍ → ℍ := fun x => elliptic L j (x + (w : ℍ)) - elliptic L j x
  have hU := (isClosed_quaternionLattice L).isOpen_compl
  have hd (x) (hx : x ∉ L) : DifferentiableAt ℝ (elliptic L j) x :=
    ((elliptic_regular L j).1.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hH (x) (hx : x ∉ L) : HasFDerivAt (𝕜 := ℝ) H 0 x := by
    have h := ((hd _ (not_mem_lattice_add L w hx)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).add_const (w : ℍ))).sub (hd x hx).hasFDerivAt
    convert! h using 1
    simp [elliptic_fderiv_add L j w hx]
  have hn : -q - (w : ℍ) ∉ L := by
    have h := not_mem_lattice_add L (-w) (q := -q) (by simpa using hq)
    simpa [sub_eq_add_neg] using h
  have he : H q = H (-q - (w : ℍ)) := hU.is_const_of_fderiv_eq_zero
    (isConnected_lattice_compl L).isPreconnected
    (fun x hx => (hH x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hH x hx).fderiv) hq hn
  have hflip : H (-q - (w : ℍ)) = -H q := by
    have harg : -q - (w : ℍ) = -(q + (w : ℍ)) := by abel
    dsimp only [H]
    rw [sub_add_cancel, harg, elliptic_even, elliptic_even, neg_sub]
  have hs : H q = -H q := he.trans hflip
  have hz : (2 : ℝ) • H q = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp hs
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (by norm_num))

/-- E2 version 2: both identities hold for every off-lattice point and every lattice period. -/
theorem E2_v2 (j : Fin 3) :
    ∀ q : ℍ, q ∉ L → ∀ w : L,
      elliptic L j (-q) = elliptic L j q ∧
      elliptic L j (q + (w : ℍ)) = elliptic L j q := by
  exact fun q hq w => ⟨elliptic_even L j q, elliptic_add L j w hq⟩

end MathResearch.Fueter
