module
public import MathResearch.Fueter.ZetaEstimates

/-! E-C2: the quaternionic zeta series and its termwise real calculus. -/
@[expose] public section
noncomputable section
open scoped Quaternion Topology BigOperators ContDiff
open Filter
namespace MathResearch.Fueter
attribute [local instance] Classical.propDecidable

/-- E-C2, with the full real Fréchet differential and intact Taylor brackets. -/
def zeta (L : Submodule ℤ ℍ) (q : ℍ) : ℍ :=
  kernel q + ∑' a : {a : L // a ≠ 0},
    (kernel (q + (a.1 : ℍ)) - kernel (a.1 : ℍ) - fderiv ℝ kernel (a.1 : ℍ) q)

/-- The sum of the differentiated brackets, including the leading kernel at index zero. -/
def zetaJetSum (L : Submodule ℤ ℍ) (l : List (Fin 4)) (q : ℍ) : ℍ :=
  ∑' a : L, zetaJet l (a : ℍ) q

theorem add_lattice_ne_zero (L : Submodule ℤ ℍ) (a : L) {q : ℍ} (hq : q ∉ L) :
    q + (a : ℍ) ≠ 0 := by
  intro he
  exact hq ((eq_neg_of_add_eq_zero_left he) ▸ L.neg_mem a.2)

variable (L : Submodule ℤ ℍ) [DiscreteTopology L] [IsZLattice ℝ L]

theorem zeta_eq_jetSum : zeta L = zetaJetSum L [] := by
  funext q
  have hs := ((zetaJet_normal_all L [] Set.univ).summable_norm (Set.mem_univ q)).of_norm
  have he := sum_single_add_tsum_ne _ hs 0
  have hb (a : {a : L // a ≠ 0}) : (a.1 : ℍ) ≠ 0 := by simpa using a.2
  simpa [zeta, zetaJetSum, zetaJet_nil _ _ (hb _), iteratedPartial] using he

theorem zetaJetSum_calculus :
    (∀ l, ContDiffOn ℝ ∞ (zetaJetSum L l) (L : Set ℍ)ᶜ) ∧
    (∀ l μ q, q ∉ L → coordPartial μ (zetaJetSum L l) q = zetaJetSum L (μ :: l) q) := by
  apply contDiffOn_tsum_of_jets _ (isClosed_quaternionLattice L).isOpen_compl
  · intro l a q hq
    exact (zetaJet_hasFDerivAt l _ q (add_lattice_ne_zero L a hq)).differentiableAt.differentiableWithinAt
  · intro l μ a q hq
    exact zetaJet_partial l μ _ q (add_lattice_ne_zero L a hq)
  · exact fun l => zetaJet_normal_all L l _

theorem zetaJet_normal_fderiv (l : List (Fin 4)) :
    NormallySummableOn (fun a : L => fderiv ℝ (zetaJet l (a : ℍ))) (L : Set ℍ)ᶜ := by
  apply normal_fderiv
  intro μ K hKU hK
  obtain ⟨u, hu, hb⟩ := zetaJet_majorant L (μ :: l) hK.isBounded
  refine ⟨u, hu, ?_⟩
  filter_upwards [hb] with a ha
  intro q hq
  rw [zetaJet_partial l μ _ _ (add_lattice_ne_zero L a (hKU hq))]
  exact ha q hq

theorem zetaJetSum_fderiv (l : List (Fin 4)) {q : ℍ} (hq : q ∉ L) :
    fderiv ℝ (zetaJetSum L l) q = ∑' a : L, fderiv ℝ (zetaJet l (a : ℍ)) q := by
  apply (hasFDerivAt_tsum_of_normal (isClosed_quaternionLattice L).isOpen_compl ?_
    (zetaJet_normal_all L l _) (zetaJet_normal_fderiv L l) hq).fderiv
  intro a x hx
  exact (zetaJet_hasFDerivAt l _ x (add_lattice_ne_zero L a hx)).differentiableAt.differentiableWithinAt

theorem zeta_regular : TwoSidedRegularOn (zeta L) (L : Set ℍ)ᶜ := by
  rw [zeta_eq_jetSum]
  have hz (C : (ℍ →L[ℝ] ℍ) →L[ℝ] ℍ)
      (hc : ∀ x ≠ 0, C (fderiv ℝ kernel x) = 0) (q : ℍ) (hq : q ∉ L) :
      C (fderiv ℝ (zetaJetSum L []) q) = 0 := by
    rw [zetaJetSum_fderiv L [] hq, C.map_tsum ((zetaJet_normal_fderiv L []).summable_norm hq).of_norm]
    suffices ht : ∀ a : L, C (fderiv ℝ (zetaJet [] (a : ℍ)) q) = 0 by
      simp only [ht, tsum_zero]
    intro a
    rw [(zetaJet_hasFDerivAt [] _ q (add_lattice_ne_zero L a hq)).fderiv, map_sub]
    simp only [iteratedPartial]
    rw [hc _ (add_lattice_ne_zero L a hq)]
    by_cases ha : (a : ℍ) = 0
    · simp [ha]
    · simp [ha, hc _ ha]
  exact ⟨(zetaJetSum_calculus L).1 [], hz leftContraction (fun x hx => kernel_left hx),
    hz rightContraction (fun x hx => kernel_right hx)⟩

theorem zeta_spatialPartial (j : Fin 3) {q : ℍ} (hq : q ∉ L) :
    coordPartial j.succ (zeta L) q = elliptic L j q := by
  rw [zeta_eq_jetSum, (zetaJetSum_calculus L).2 [] j.succ q hq, elliptic_eq_tsum]
  exact tsum_congr fun a => zetaJet_spatial j (a : ℍ) q

theorem zeta_iteratedPartial (l : List (Fin 4)) {q : ℍ} (hq : q ∉ L) :
    iteratedPartial l (zeta L) q = zetaJetSum L l q := by
  rw [zeta_eq_jetSum]
  exact iteratedPartial_of_jets (zetaJetSum L) (isClosed_quaternionLattice L).isOpen_compl
    (zetaJetSum_calculus L).2 l hq

omit [IsZLattice ℝ L] in
theorem zeta_summand_iteratedPartial (l : List (Fin 4)) (a : L) {q : ℍ} (hq : q ∉ L) :
    iteratedPartial l (zetaJet [] (a : ℍ)) q = zetaJet l (a : ℍ) q := by
  exact iteratedPartial_of_jets (fun l => zetaJet l (a : ℍ))
    (isClosed_quaternionLattice L).isOpen_compl
    (fun l μ x hx => zetaJet_partial l μ _ x (add_lattice_ne_zero L a hx)) l hq

theorem zeta_termwise_normal (l : List (Fin 4)) :
    NormallySummableOn (fun a : L => iteratedPartial l (zetaJet [] (a : ℍ))) (L : Set ℍ)ᶜ := by
  intro K hKU hK
  obtain ⟨u, hu, hb⟩ := zetaJet_majorant L l hK.isBounded
  refine ⟨u, hu, ?_⟩
  filter_upwards [hb] with a ha
  intro q hq
  rw [zeta_summand_iteratedPartial L l a (hKU hq)]
  exact ha q hq

theorem zeta_termwise_tsum (l : List (Fin 4)) {q : ℍ} (hq : q ∉ L) :
    (∑' a : L, iteratedPartial l (zetaJet [] (a : ℍ)) q) = iteratedPartial l (zeta L) q := by
  rw [zeta_iteratedPartial L l hq]
  exact tsum_congr fun a => zeta_summand_iteratedPartial L l a hq

theorem zeta_termwise_locallyUniform (l : List (Fin 4)) :
    HasSumLocallyUniformlyOn (fun a : L => iteratedPartial l (zetaJet [] (a : ℍ)))
      (iteratedPartial l (zeta L)) (L : Set ℍ)ᶜ :=
  ((zeta_termwise_normal L l).hasSumLocallyUniformlyOn
    (isClosed_quaternionLattice L).isOpen_compl).congr_right
      (fun _ hq => zeta_termwise_tsum L l hq)

theorem zeta_termwise_uniformOn (l : List (Fin 4)) {K : Set ℍ}
    (hK : IsCompact K) (hKL : K ⊆ (L : Set ℍ)ᶜ) :
    TendstoUniformlyOn (fun s : Finset L => fun q =>
      ∑ a ∈ s, iteratedPartial l (zetaJet [] (a : ℍ)) q)
      (iteratedPartial l (zeta L)) atTop K := by
  obtain ⟨u, hu, hb⟩ := zeta_termwise_normal L l K hKL hK
  exact (tendstoUniformlyOn_tsum_of_cofinite_eventually hu hb).congr_right
    (fun q hq => zeta_termwise_tsum L l (hKL hq))

end MathResearch.Fueter
