module

public import MathResearch.Fueter.EllipticRegularity

/-! The exact E-C1 construction and E1 version 2. -/
@[expose] public section
noncomputable section
open scoped Quaternion Topology BigOperators ContDiff
open Filter
namespace MathResearch.Fueter

/-- E-C1: the leading term and the sum of intact regularized brackets.
Lean indices `0,1,2` represent the article's spatial indices `1,2,3`. -/
def elliptic (L : Submodule ℤ ℍ) (j : Fin 3) (q : ℍ) : ℍ :=
  kernelSpatialPartial j q + ∑' a : {a : L // a ≠ 0},
    (kernelSpatialPartial j (q + (a.1 : ℍ)) - kernelSpatialPartial j (a.1 : ℍ))

theorem iteratedPartial_of_jets (F : List (Fin 4) → ℍ → ℍ) {U : Set ℍ}
    (hU : IsOpen U)
    (hp : ∀ l μ q, q ∈ U → coordPartial μ (F l) q = F (μ :: l) q)
    (l : List (Fin 4)) {q : ℍ} (hq : q ∈ U) :
    iteratedPartial l (F []) q = F l q := by
  induction l generalizing q with
  | nil => rfl
  | cons μ l ih =>
    have he : iteratedPartial l (F []) =ᶠ[𝓝 q] F l :=
      eventually_of_mem (hU.mem_nhds hq) fun x hx => ih hx
    change fderiv ℝ (iteratedPartial l (F [])) q (coordinateBasis μ) = _
    rw [he.fderiv_eq]
    exact hp l μ q hq

/-- Separate one summand using the literal non-equality subtype. -/
theorem sum_single_add_tsum_ne {ι : Type*} (f : ι → ℍ) (hf : Summable f) (a : ι) :
    f a + (∑' b : {b : ι // b ≠ a}, f b.1) = ∑' b, f b := by
  classical
  let e : {b : ι // b ≠ a} ≃ {b : ι // b ∉ ({a} : Finset ι)} :=
    Equiv.subtypeEquivRight (fun b => by simp)
  calc
    _ = f a + (∑' b : {b : ι // b ∉ ({a} : Finset ι)}, f b.1) :=
      congrArg (fun z => f a + z) (e.tsum_eq (fun b => f b.1))
    _ = _ := by simpa only [Finset.sum_singleton] using hf.sum_add_tsum_subtype_compl {a}

variable (L : Submodule ℤ ℍ) [DiscreteTopology L] [IsZLattice ℝ L]

theorem elliptic_eq_tsum (j : Fin 3) (q : ℍ) :
    elliptic L j q = ∑' a : L, regularizedJet j [] (a : ℍ) q := by
  classical
  have hs := ((regularizedJet_normal_all L j [] Set.univ).summable_norm (Set.mem_univ q)).of_norm
  have he := sum_single_add_tsum_ne _ hs 0
  have hb (a : {a : L // a ≠ 0}) : (a.1 : ℍ) ≠ 0 := by simpa using a.2
  simpa [elliptic, regularizedJet, hb] using he

theorem elliptic_eq_jetSum (j : Fin 3) : elliptic L j = ellipticJetSum L Set.univ j [] := by
  funext q
  rw [elliptic_eq_tsum]
  exact ((Equiv.Set.univ L).tsum_eq (fun a : L => regularizedJet j [] (a : ℍ) q)).symm

theorem elliptic_regular (j : Fin 3) : TwoSidedRegularOn (elliptic L j) (L : Set ℍ)ᶜ := by
  rw [elliptic_eq_jetSum]
  simpa using ellipticJetSum_regular L Set.univ j []

theorem elliptic_iteratedPartial (j : Fin 3) (l : List (Fin 4)) {q : ℍ} (hq : q ∉ L) :
    iteratedPartial l (elliptic L j) q = ∑' a : L, regularizedJet j l (a : ℍ) q := by
  rw [elliptic_eq_jetSum]
  have h := iteratedPartial_of_jets (ellipticJetSum L Set.univ j)
    (isOpen_latticeSeriesDomain L Set.univ) (ellipticJetSum_calculus L Set.univ j).2 l
    (by simpa using hq)
  exact h.trans ((Equiv.Set.univ L).tsum_eq (fun a : L => regularizedJet j l (a : ℍ) q))

omit [IsZLattice ℝ L] in
theorem elliptic_summand_iteratedPartial (j : Fin 3) (l : List (Fin 4)) (a : L)
    {q : ℍ} (hq : q ∉ L) :
    iteratedPartial l (regularizedJet j [] (a : ℍ)) q = regularizedJet j l (a : ℍ) q := by
  apply iteratedPartial_of_jets (fun l => regularizedJet j l (a : ℍ))
    (isClosed_quaternionLattice L).isOpen_compl _ l hq
  intro l μ x hx
  apply regularizedJet_partial
  intro he
  exact hx ((eq_neg_of_add_eq_zero_left he) ▸ L.neg_mem a.2)

theorem elliptic_termwise_normal (j : Fin 3) (l : List (Fin 4)) :
    NormallySummableOn (fun a : L => iteratedPartial l (regularizedJet j [] (a : ℍ)))
      (L : Set ℍ)ᶜ := by
  intro K hKU hK
  obtain ⟨u, hu, hb⟩ := regularizedJet_majorant L j l hK.isBounded
  refine ⟨u, hu, ?_⟩
  filter_upwards [hb] with a ha
  intro q hq
  rw [elliptic_summand_iteratedPartial L j l a (hKU hq)]
  exact ha q hq

theorem elliptic_termwise_tsum (j : Fin 3) (l : List (Fin 4)) {q : ℍ} (hq : q ∉ L) :
    (∑' a : L, iteratedPartial l (regularizedJet j [] (a : ℍ)) q) =
      iteratedPartial l (elliptic L j) q := by
  rw [elliptic_iteratedPartial L j l hq]
  exact tsum_congr fun a => elliptic_summand_iteratedPartial L j l a hq

theorem elliptic_termwise_locallyUniform (j : Fin 3) (l : List (Fin 4)) :
    HasSumLocallyUniformlyOn
      (fun a : L => iteratedPartial l (regularizedJet j [] (a : ℍ)))
      (iteratedPartial l (elliptic L j)) (L : Set ℍ)ᶜ :=
  ((elliptic_termwise_normal L j l).hasSumLocallyUniformlyOn
    (isClosed_quaternionLattice L).isOpen_compl).congr_right
      (fun _ hq => elliptic_termwise_tsum L j l hq)

theorem elliptic_termwise_uniformOn (j : Fin 3) (l : List (Fin 4)) {K : Set ℍ}
    (hK : IsCompact K) (hKL : K ⊆ (L : Set ℍ)ᶜ) :
    TendstoUniformlyOn (fun s : Finset L => fun q =>
      ∑ a ∈ s, iteratedPartial l (regularizedJet j [] (a : ℍ)) q)
      (iteratedPartial l (elliptic L j)) atTop K := by
  obtain ⟨u, hu, hb⟩ := elliptic_termwise_normal L j l K hKL hK
  exact (tendstoUniformlyOn_tsum_of_cofinite_eventually hu hb).congr_right
    (fun q hq => elliptic_termwise_tsum L j l (hKL hq))

theorem TwoSidedRegularOn.sub_const {U : Set ℍ} (hU : IsOpen U) {f : ℍ → ℍ}
    (hf : TwoSidedRegularOn f U) (c : ℍ) : TwoSidedRegularOn (fun q => f q - c) U := by
  have he (q) (hq : q ∈ U) : fderiv ℝ (fun x => f x - c) q = fderiv ℝ f q :=
    (((hf.1.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt.sub_const c).fderiv
  refine ⟨hf.1.sub contDiffOn_const, ?_, ?_⟩
  · intro q hq; simpa only [leftOperator, he q hq] using hf.2.1 q hq
  · intro q hq; simpa only [rightOperator, he q hq] using hf.2.2 q hq

/-- Removing the single pole at `w` leaves a smooth two-sided regular function on an open
neighborhood of that pole. The equality is required on the original off-lattice domain. -/
theorem elliptic_regular_remainder (j : Fin 3) (w : L) :
    ∃ U : Set ℍ, IsOpen U ∧ (w : ℍ) ∈ U ∧ ∃ r : ℍ → ℍ,
      TwoSidedRegularOn r U ∧ ∀ q ∈ U, q ∉ L →
        r q = elliptic L j q - kernelSpatialPartial j (q - (w : ℍ)) := by
  classical
  let S : Set L := {a | a ≠ -w}
  let U := latticeSeriesDomain L S
  let c : ℍ := if -(w : ℍ) ≠ 0 then kernelSpatialPartial j (-(w : ℍ)) else 0
  refine ⟨U, isOpen_latticeSeriesDomain L S, ?_,
    fun q => ellipticJetSum L S j [] q - c,
    (ellipticJetSum_regular L S j []).sub_const (isOpen_latticeSeriesDomain L S) c, ?_⟩
  · apply (mem_latticeSeriesDomain L S (w : ℍ)).mpr
    intro a he
    exact a.2 (Subtype.ext (eq_neg_of_add_eq_zero_right he))
  · intro q _ _
    have hs := ((regularizedJet_normal_all L j [] Set.univ).summable_norm (Set.mem_univ q)).of_norm
    have he := sum_single_add_tsum_ne _ hs (-w)
    have he' : regularizedJet j [] (-(w : ℍ)) q + ellipticJetSum L S j [] q = elliptic L j q := by
      rw [elliptic_eq_tsum]
      convert! he using 1
    rw [← he']
    simp only [regularizedJet, kernelJet_nil, true_and, sub_eq_add_neg, c]
    abel

/-- E1 version 2. Absolute convergence and uniform convergence on compact sets are stated
for the original summands and every ordered real derivative. The zero lattice index is the
leading `G_j(q)` term of E-C1; all nonzero indices remain intact brackets. -/
theorem E1_v2 (j : Fin 3) :
    (∀ l : List (Fin 4), ∀ q : ℍ, q ∉ L →
      Summable (fun a : L => ‖iteratedPartial l (regularizedJet j [] (a : ℍ)) q‖)) ∧
    (∀ l : List (Fin 4), ∀ K : Set ℍ, IsCompact K → K ⊆ (L : Set ℍ)ᶜ →
      TendstoUniformlyOn (fun s : Finset L => fun q =>
        ∑ a ∈ s, iteratedPartial l (regularizedJet j [] (a : ℍ)) q)
        (iteratedPartial l (elliptic L j)) atTop K) ∧
    (∀ l : List (Fin 4), HasSumLocallyUniformlyOn
      (fun a : L => iteratedPartial l (regularizedJet j [] (a : ℍ)))
      (iteratedPartial l (elliptic L j)) (L : Set ℍ)ᶜ) ∧
    TwoSidedRegularOn (elliptic L j) (L : Set ℍ)ᶜ ∧
    (∀ w : L, ∃ U : Set ℍ, IsOpen U ∧ (w : ℍ) ∈ U ∧ ∃ r : ℍ → ℍ,
      TwoSidedRegularOn r U ∧ ∀ q ∈ U, q ∉ L →
        r q = elliptic L j q - kernelSpatialPartial j (q - (w : ℍ))) := by
  exact ⟨fun l _ hq => (elliptic_termwise_normal L j l).summable_norm hq,
    fun l _ hK hKL => elliptic_termwise_uniformOn L j l hK hKL,
    elliptic_termwise_locallyUniform L j, elliptic_regular L j, elliptic_regular_remainder L j⟩

end MathResearch.Fueter
