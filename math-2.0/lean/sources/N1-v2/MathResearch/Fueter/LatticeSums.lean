module

public import MathResearch.Fueter.KernelEstimates
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-! N2 and N3: convergent higher quaternionic lattice sums and parity cancellation. -/

@[expose] public section
noncomputable section
open scoped Quaternion Topology BigOperators
open Filter

namespace MathResearch.Fueter

/-- Embed a spatial multi-index in the four real coordinates, with time order zero.
The Lean indices `0,1,2` denote the article's coordinates `x₁,x₂,x₃`. -/
def spatialMultiIndex (ν : Fin 3 → ℕ) : Fin 4 → ℕ := Fin.cons 0 ν

@[simp] theorem sum_spatialMultiIndex (ν : Fin 3 → ℕ) :
    ∑ μ, spatialMultiIndex ν μ = ∑ j, ν j := by
  simp [spatialMultiIndex, Fin.sum_univ_succ]

/-- The function `G_ν = ∂₁^ν₁ ∂₂^ν₂ ∂₃^ν₃ G` of N-D1. -/
def higherKernel (ν : Fin 3 → ℕ) : ℍ → ℍ := multiIndexPartial (spatialMultiIndex ν) kernel

/-- F2 specialized to every spatial multi-index. -/
theorem higherKernel_norm_le (ν : Fin 3 → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℍ, q ≠ 0 →
      ‖higherKernel ν q‖ ≤ C * ‖q‖⁻¹ ^ (3 + ∑ j, ν j) := by
  simpa [higherKernel, inv_pow] using kernel_multiIndexPartial_norm_le (spatialMultiIndex ν)

/-- The spatial parity formula, including every derivative order. -/
theorem higherKernel_neg (ν : Fin 3 → ℕ) (q : ℍ) (hq : q ≠ 0) :
    higherKernel ν (-q) = (-1 : ℝ) ^ ((∑ j, ν j) + 1) • higherKernel ν q := by
  simpa [higherKernel] using kernel_multiIndexPartial_neg (spatialMultiIndex ν) q hq

variable (L : Submodule ℤ ℍ) [DiscreteTopology L] [IsZLattice ℝ L]

/-- A full quaternionic lattice has integer rank four, using mathlib's lattice API. -/
theorem quaternionLattice_rank : Module.finrank ℤ L = 4 := by
  rw [ZLattice.rank ℝ L, Quaternion.finrank_eq_four]

omit [IsZLattice ℝ L] in
/-- A discrete quaternionic lattice is closed in the ambient real space. -/
theorem isClosed_quaternionLattice : IsClosed (L : Set ℍ) :=
  L.toAddSubgroup.isClosed_of_discreteTopology

/-- The absolutely convergent Eisenstein sum of N-C1, indexed only by nonzero lattice points. -/
def eisensteinCoefficient (ν : Fin 3 → ℕ) : ℍ :=
  ∑' l : {l : L // l ≠ 0}, higherKernel ν (l.1 : ℍ)

/-- The translated higher-kernel series before subtracting its constant coefficient. -/
def higherLatticeSum (ν : Fin 3 → ℕ) (q : ℍ) : ℍ :=
  ∑' l : L, higherKernel ν (q + (l : ℍ))

/-- The function `wp_{L,ν}` of N-C1. Convergence is proved below for `|ν| ≥ 2`.
Its mathematical domain is the complement of the lattice. -/
def higherElliptic (ν : Fin 3 → ℕ) (q : ℍ) : ℍ :=
  higherLatticeSum L ν q - eisensteinCoefficient L ν

/-- The reciprocal-power majorant is summable once its exponent exceeds four. -/
theorem summable_lattice_inv_pow (n : ℕ) (hn : 4 < n) :
    Summable (fun l : L => ‖(l : ℍ)‖⁻¹ ^ n) := by
  simpa using ZLattice.summable_norm_sub_inv_pow L n
    (by rwa [quaternionLattice_rank L]) 0

/-- Absolute convergence of `E_ν` from F2 and mathlib's lattice p-series theorem. -/
theorem summable_norm_eisenstein (ν : Fin 3 → ℕ) (hν : 2 ≤ ∑ j, ν j) :
    Summable (fun l : {l : L // l ≠ 0} => ‖higherKernel ν (l.1 : ℍ)‖) := by
  obtain ⟨C, hC, hbound⟩ := higherKernel_norm_le ν
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (((summable_lattice_inv_pow L (3 + ∑ j, ν j) (by omega)).mul_left C).subtype (· ≠ 0))
  intro l
  exact hbound _ (by simpa using l.2)

/-- A reciprocal-power decay bound gives a summable majorant uniformly on any
bounded set, after omitting finitely many lattice points. This is the reusable
analytic step; no quaternionic multiplication is involved. -/
theorem lattice_decay_majorant {f : ℍ → ℍ} {n : ℕ} (hn : 4 < n)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ x : ℍ, x ≠ 0 → ‖f x‖ ≤ C * ‖x‖⁻¹ ^ n)
    {K : Set ℍ} (hK : Bornology.IsBounded K) :
    ∃ u : L → ℝ, Summable u ∧
      ∀ᶠ l : L in cofinite, ∀ q ∈ K, ‖f (q + (l : ℍ))‖ ≤ u l := by
  let : ProperSpace L := .of_isClosed (isClosed_quaternionLattice L)
  obtain ⟨R, hR, hRK⟩ := hK.exists_pos_norm_le
  refine ⟨fun l => (C * 2 ^ n) * ‖(l : ℍ)‖⁻¹ ^ n,
    (summable_lattice_inv_pow L n hn).mul_left _, ?_⟩
  have hlarge : ∀ᶠ l : L in cofinite, 2 * R + 1 < ‖(l : ℍ)‖ := by
    rw [eventually_cofinite]
    simp only [not_lt]
    change {l : L | ‖l‖ ≤ 2 * R + 1}.Finite
    simpa only [Metric.closedBall, dist_zero_right] using
      (isCompact_iff_finite.mp (isCompact_closedBall (0 : L) (2 * R + 1)))
  filter_upwards [hlarge] with l hl
  intro q hq
  have hqR := hRK q hq
  have hnorm : ‖(l : ℍ)‖ - ‖q‖ ≤ ‖q + (l : ℍ)‖ := by
    simpa [sub_neg_eq_add, add_comm] using norm_sub_norm_le (l : ℍ) (-q)
  have hpos : 0 < ‖q + (l : ℍ)‖ := by linarith
  have hhalf : ‖(l : ℍ)‖ / 2 ≤ ‖q + (l : ℍ)‖ := by linarith
  have hlpos : 0 < ‖(l : ℍ)‖ := by linarith
  calc
    ‖f (q + (l : ℍ))‖ ≤ C * ‖q + (l : ℍ)‖⁻¹ ^ n :=
      hf _ (norm_pos_iff.mp hpos)
    _ ≤ C * (‖(l : ℍ)‖ / 2)⁻¹ ^ n := by gcongr
    _ = (C * 2 ^ n) * ‖(l : ℍ)‖⁻¹ ^ n := by rw [inv_div, div_eq_mul_inv, mul_pow]; ring

/-- Absolute convergence of the translated series at every point outside the lattice. -/
theorem summable_norm_higherLatticeSum (ν : Fin 3 → ℕ) (hν : 2 ≤ ∑ j, ν j)
    (q : ℍ) (hq : q ∉ L) :
    Summable (fun l : L => ‖higherKernel ν (q + (l : ℍ))‖) := by
  obtain ⟨C, hC, hbound⟩ := higherKernel_norm_le ν
  have hn : Module.finrank ℤ L < 3 + ∑ j, ν j := by rw [quaternionLattice_rank L]; omega
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((ZLattice.summable_norm_sub_inv_pow L _ hn (-q)).mul_left C)
  intro l
  have hne : q + (l : ℍ) ≠ 0 := by
    intro h
    have : q = -(l : ℍ) := eq_neg_of_add_eq_zero_left h
    exact hq (this ▸ L.neg_mem l.2)
  simpa [sub_neg_eq_add, add_comm] using hbound _ hne

/-- Uniform convergence on every compact subset of the complement of the lattice. -/
theorem higherLatticeSum_uniformOn (ν : Fin 3 → ℕ) (hν : 2 ≤ ∑ j, ν j)
    {K : Set ℍ} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun s : Finset L => fun q => ∑ l ∈ s, higherKernel ν (q + (l : ℍ)))
      (higherLatticeSum L ν) atTop K := by
  obtain ⟨C, hC, hbound⟩ := higherKernel_norm_le ν
  obtain ⟨u, hu, hfu⟩ := lattice_decay_majorant L (by omega) hC hbound hK.isBounded
  exact tendstoUniformlyOn_tsum_of_cofinite_eventually hu hfu

/-- N2's local uniform convergence, expressed with mathlib's standard series notion. -/
theorem higherLatticeSum_locallyUniform (ν : Fin 3 → ℕ) (hν : 2 ≤ ∑ j, ν j) :
    HasSumLocallyUniformlyOn (fun l : L => fun q => higherKernel ν (q + (l : ℍ)))
      (higherLatticeSum L ν) (L : Set ℍ)ᶜ := by
  apply hasSumLocallyUniformlyOn_of_forall_compact (isClosed_quaternionLattice L).isOpen_compl
  intro K _ hK
  exact hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr (higherLatticeSum_uniformOn L ν hν hK)

omit [DiscreteTopology L] [IsZLattice ℝ L] in
/-- Translation reindexes the lattice. N2 separately supplies absolute convergence. -/
theorem higherLatticeSum_add (ν : Fin 3 → ℕ) (ω : L) (q : ℍ) :
    higherLatticeSum L ν (q + (ω : ℍ)) = higherLatticeSum L ν q := by
  simpa [higherLatticeSum, add_assoc] using
    (Equiv.addLeft ω).tsum_eq (fun l : L => higherKernel ν (q + (l : ℍ)))

omit [DiscreteTopology L] [IsZLattice ℝ L] in
/-- Subtracting the constant Eisenstein coefficient preserves periodicity. -/
theorem higherElliptic_add (ν : Fin 3 → ℕ) (ω : L) (q : ℍ) :
    higherElliptic L ν (q + (ω : ℍ)) = higherElliptic L ν q := by
  simp only [higherElliptic, higherLatticeSum_add]

/-- N2 version 1: absolute convergence of the coefficient and translated sums,
local uniform convergence off the lattice, and periodicity for every lattice period. -/
theorem N2_v1 (ν : Fin 3 → ℕ) (hν : 2 ≤ ∑ j, ν j) :
    Summable (fun l : {l : L // l ≠ 0} => ‖higherKernel ν (l.1 : ℍ)‖) ∧
    (∀ q : ℍ, q ∉ L → Summable (fun l : L => ‖higherKernel ν (q + (l : ℍ))‖)) ∧
    HasSumLocallyUniformlyOn (fun l : L => fun q => higherKernel ν (q + (l : ℍ)))
      (higherLatticeSum L ν) (L : Set ℍ)ᶜ ∧
    (∀ ω : L, ∀ q : ℍ, q ∉ L →
      higherElliptic L ν (q + (ω : ℍ)) = higherElliptic L ν q) := by
  exact ⟨summable_norm_eisenstein L ν hν, summable_norm_higherLatticeSum L ν hν,
    higherLatticeSum_locallyUniform L ν hν, fun ω q _ => higherElliptic_add L ν ω q⟩

/-- Negation permutes the nonzero lattice points without changing the index set. -/
def nonzeroLatticeNeg : {l : L // l ≠ 0} ≃ {l : L // l ≠ 0} where
  toFun l := ⟨-l.1, neg_ne_zero.mpr l.2⟩
  invFun l := ⟨-l.1, neg_ne_zero.mpr l.2⟩
  left_inv l := by simp
  right_inv l := by simp

/-- N3 version 1: every absolutely convergent coefficient of even spatial order vanishes.
The proof uses the convergent sum from N2, so the conclusion is not a consequence
of Lean's default value for a divergent `tsum`. -/
theorem N3_v1 (ν : Fin 3 → ℕ) (hν : 2 ≤ ∑ j, ν j) (heven : Even (∑ j, ν j)) :
    eisensteinCoefficient L ν = 0 := by
  have hs : HasSum (fun l : {l : L // l ≠ 0} => higherKernel ν (l.1 : ℍ))
      (eisensteinCoefficient L ν) := (summable_norm_eisenstein L ν hν).of_norm.hasSum
  have hn : HasSum (fun l : {l : L // l ≠ 0} => -higherKernel ν (l.1 : ℍ))
      (eisensteinCoefficient L ν) := by
    have h := (nonzeroLatticeNeg L).hasSum_iff.mpr hs
    convert h using 1
    funext l
    change -higherKernel ν (l.1 : ℍ) = higherKernel ν (-(l.1 : ℍ))
    rw [higherKernel_neg ν _ (by simpa using l.2), heven.add_one.neg_one_pow, neg_one_smul]
  have heq := hn.unique hs.neg
  have htwo : (2 : ℝ) • eisensteinCoefficient L ν = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp heq
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

end MathResearch.Fueter
