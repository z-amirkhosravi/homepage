module

public import MathResearch.Fueter.EllipticEstimates

/-! E1: the regularized elliptic series, all real derivatives, and regular remainders at poles. -/
@[expose] public section
noncomputable section
open scoped Quaternion Topology BigOperators ContDiff
open Filter
namespace MathResearch.Fueter

/-- The domain avoiding precisely the poles indexed by `S`. -/
def latticeSeriesDomain (L : Submodule ℤ ℍ) (S : Set L) : Set ℍ :=
  (fun q : ℍ => -q) ⁻¹' (Subtype.val '' S)ᶜ

theorem mem_latticeSeriesDomain (L : Submodule ℤ ℍ) (S : Set L) (q : ℍ) :
    q ∈ latticeSeriesDomain L S ↔ ∀ a : S, q + (a.1 : ℍ) ≠ 0 := by
  constructor
  · intro h a he
    exact h ⟨a.1, a.2, eq_neg_of_add_eq_zero_right he⟩
  · intro h ⟨a, ha, he⟩
    exact h ⟨a, ha⟩ (by rw [he]; simp)

theorem isOpen_latticeSeriesDomain (L : Submodule ℤ ℍ) [DiscreteTopology L] (S : Set L) :
    IsOpen (latticeSeriesDomain L S) :=
  ((isClosed_quaternionLattice L).isClosedMap_subtype_val S
    (isClosed_discrete S)).isOpen_compl.preimage continuous_neg

@[simp] theorem latticeSeriesDomain_univ (L : Submodule ℤ ℍ) :
    latticeSeriesDomain L Set.univ = (L : Set ℍ)ᶜ := by
  ext q
  simp [latticeSeriesDomain]

theorem regularizedJet_hasFDerivAt (j : Fin 3) (l : List (Fin 4)) (a q : ℍ)
    (hq : q + a ≠ 0) :
    HasFDerivAt (regularizedJet j l a) (fderiv ℝ (kernelJet j l) (q + a)) q := by
  classical
  have h := ((kernelJet_regular j l).1.contDiffAt
    (isOpen_punctured.mem_nhds hq)).differentiableAt (by simp)
  unfold regularizedJet
  convert!
    ((h.hasFDerivAt.comp q ((hasFDerivAt_id q).add_const a)).sub_const
      (if l = [] ∧ a ≠ 0 then kernelSpatialPartial j a else 0)) using 1

theorem regularizedJet_partial (j : Fin 3) (l : List (Fin 4)) (μ : Fin 4) (a q : ℍ)
    (hq : q + a ≠ 0) :
    coordPartial μ (regularizedJet j l a) q = regularizedJet j (μ :: l) a q := by
  simp only [coordPartial, directional, (regularizedJet_hasFDerivAt j l a q hq).fderiv,
    regularizedJet_cons, kernelJet_cons]

theorem regularizedJet_regular (j : Fin 3) (l : List (Fin 4)) (a : ℍ)
    {U : Set ℍ} (hU : ∀ q ∈ U, q + a ≠ 0) :
    TwoSidedRegularOn (regularizedJet j l a) U := by
  refine ⟨?_, ?_, ?_⟩
  · exact ((kernelJet_regular j l).1.comp
      (contDiffOn_id.add contDiffOn_const) hU).sub contDiffOn_const
  · intro q hq
    change leftContraction (fderiv ℝ (regularizedJet j l a) q) = 0
    rw [(regularizedJet_hasFDerivAt j l a q (hU q hq)).fderiv]
    exact (kernelJet_regular j l).2.1 _ (hU q hq)
  · intro q hq
    change rightContraction (fderiv ℝ (regularizedJet j l a) q) = 0
    rw [(regularizedJet_hasFDerivAt j l a q (hU q hq)).fderiv]
    exact (kernelJet_regular j l).2.2 _ (hU q hq)

/-- A subseries, including the series with one pole removed. -/
def ellipticJetSum (L : Submodule ℤ ℍ) (S : Set L) (j : Fin 3) (l : List (Fin 4))
    (q : ℍ) : ℍ := ∑' a : S, regularizedJet j l (a.1 : ℍ) q

variable (L : Submodule ℤ ℍ) [DiscreteTopology L] [IsZLattice ℝ L]

theorem ellipticJetSum_calculus (S : Set L) (j : Fin 3) :
    (∀ l, ContDiffOn ℝ ∞ (ellipticJetSum L S j l) (latticeSeriesDomain L S)) ∧
    (∀ l μ q, q ∈ latticeSeriesDomain L S →
      coordPartial μ (ellipticJetSum L S j l) q = ellipticJetSum L S j (μ :: l) q) := by
  apply contDiffOn_tsum_of_jets _ (isOpen_latticeSeriesDomain L S)
  · intro l a q hq
    exact (regularizedJet_hasFDerivAt j l (a.1 : ℍ) q
      ((mem_latticeSeriesDomain L S q).mp hq a)).differentiableAt.differentiableWithinAt
  · intro l μ a q hq
    exact regularizedJet_partial j l μ (a.1 : ℍ) q ((mem_latticeSeriesDomain L S q).mp hq a)
  · exact fun l => regularizedJet_normal L j l S _

theorem ellipticJetSum_fderiv (S : Set L) (j : Fin 3) (l : List (Fin 4))
    {q : ℍ} (hq : q ∈ latticeSeriesDomain L S) :
    fderiv ℝ (ellipticJetSum L S j l) q =
      ∑' a : S, fderiv ℝ (regularizedJet j l (a.1 : ℍ)) q := by
  apply (hasFDerivAt_tsum_of_normal (isOpen_latticeSeriesDomain L S) ?_
    (regularizedJet_normal L j l S _) ?_ hq).fderiv
  · intro a x hx
    exact (regularizedJet_hasFDerivAt j l (a.1 : ℍ) x
      ((mem_latticeSeriesDomain L S x).mp hx a)).differentiableAt.differentiableWithinAt
  · apply normal_fderiv
    intro μ K hKU hK
    obtain ⟨u, hu, hb⟩ := regularizedJet_normal L j (μ :: l) S _ K hKU hK
    refine ⟨u, hu, ?_⟩
    filter_upwards [hb] with a ha
    intro x hx
    rw [regularizedJet_partial j l μ _ _ ((mem_latticeSeriesDomain L S x).mp (hKU hx) a)]
    exact ha x hx

theorem ellipticJetSum_regular (S : Set L) (j : Fin 3) (l : List (Fin 4)) :
    TwoSidedRegularOn (ellipticJetSum L S j l) (latticeSeriesDomain L S) := by
  have hn : NormallySummableOn
      (fun a : S => fderiv ℝ (regularizedJet j l (a.1 : ℍ))) (latticeSeriesDomain L S) := by
    apply normal_fderiv
    intro μ K hKU hK
    obtain ⟨u, hu, hb⟩ := regularizedJet_normal L j (μ :: l) S _ K hKU hK
    refine ⟨u, hu, ?_⟩
    filter_upwards [hb] with a ha
    intro q hq
    rw [regularizedJet_partial j l μ _ _ ((mem_latticeSeriesDomain L S q).mp (hKU hq) a)]
    exact ha q hq
  have hz (C : (ℍ →L[ℝ] ℍ) →L[ℝ] ℍ)
      (hc : ∀ a : S, ∀ q ∈ latticeSeriesDomain L S,
        C (fderiv ℝ (regularizedJet j l (a.1 : ℍ)) q) = 0)
      (q) (hq : q ∈ latticeSeriesDomain L S) :
      C (fderiv ℝ (ellipticJetSum L S j l) q) = 0 := by
    rw [ellipticJetSum_fderiv L S j l hq, C.map_tsum (hn.summable_norm hq).of_norm]
    simp only [hc _ q hq, tsum_zero]
  refine ⟨(ellipticJetSum_calculus L S j).1 l, ?_, ?_⟩
  · exact hz leftContraction fun a => (regularizedJet_regular j l (a.1 : ℍ)
      (fun q hq => (mem_latticeSeriesDomain L S q).mp hq a)).2.1
  · exact hz rightContraction fun a => (regularizedJet_regular j l (a.1 : ℍ)
      (fun q hq => (mem_latticeSeriesDomain L S q).mp hq a)).2.2

end MathResearch.Fueter
