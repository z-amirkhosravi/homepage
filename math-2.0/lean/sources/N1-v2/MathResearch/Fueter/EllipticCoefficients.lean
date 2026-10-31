module

public import MathResearch.Fueter.PartialCommutation

/-! N1: the derivatives at zero of the smooth elliptic remainder are Eisenstein coefficients. -/
@[expose] public section
noncomputable section
open scoped Quaternion Topology BigOperators ContDiff
open Filter
namespace MathResearch.Fueter

/-- Remove the zero-index singular term from the E-C1 series. -/
def ellipticRegularPart (L : Submodule ℤ ℍ) (j : Fin 3) : ℍ → ℍ :=
  ellipticJetSum L {a | a ≠ 0} j []

/-- The open domain on which the series with the pole at zero removed is regular. -/
def ellipticRegularPartDomain (L : Submodule ℤ ℍ) : Set ℍ :=
  latticeSeriesDomain L {a | a ≠ 0}

theorem ellipticRegularPart_eq (L : Submodule ℤ ℍ) (j : Fin 3) (q : ℍ) :
    ellipticRegularPart L j q = ∑' a : {a : L // a ≠ 0},
      (kernelSpatialPartial j (q + (a.1 : ℍ)) - kernelSpatialPartial j (a.1 : ℍ)) := by
  unfold ellipticRegularPart ellipticJetSum
  apply tsum_congr
  intro a
  have ha : (a.1 : ℍ) ≠ 0 := fun he => a.2 (Subtype.ext he)
  simp [regularizedJet, ha]

theorem ellipticRegularPart_eq_sub (L : Submodule ℤ ℍ) (j : Fin 3) (q : ℍ) :
    ellipticRegularPart L j q = elliptic L j q - kernelSpatialPartial j q := by
  rw [elliptic, ellipticRegularPart_eq]
  abel

theorem zero_mem_ellipticRegularPartDomain (L : Submodule ℤ ℍ) :
    (0 : ℍ) ∈ ellipticRegularPartDomain L := by
  apply (mem_latticeSeriesDomain L _ 0).mpr
  intro a
  simp only [zero_add]
  exact fun he => a.2 (Subtype.ext he)

theorem not_mem_lattice_of_mem_regularPartDomain (L : Submodule ℤ ℍ) {q : ℍ}
    (hq : q ∈ ellipticRegularPartDomain L) (h0 : q ≠ 0) : q ∉ L := by
  intro hL
  let a : {a : L // a ≠ 0} := ⟨⟨-q, L.neg_mem hL⟩, by simpa using h0⟩
  exact (mem_latticeSeriesDomain L _ q).mp hq a (by simp [a])

theorem sum_spatial_add_single (μ : Fin 3 → ℕ) (j : Fin 3) :
    (∑ i : Fin 3, (μ + Pi.single j 1 : Fin 3 → ℕ) i) = (∑ i, μ i) + 1 := by
  fin_cases j <;> simp [Fin.sum_univ_succ, Pi.add_apply, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]

variable (L : Submodule ℤ ℍ) [DiscreteTopology L] [IsZLattice ℝ L]

omit [IsZLattice ℝ L] in
theorem isOpen_ellipticRegularPartDomain : IsOpen (ellipticRegularPartDomain L) :=
  isOpen_latticeSeriesDomain L _

/-- This explicit remainder is the smooth, two-sided regular extension at zero promised by E1. -/
theorem ellipticRegularPart_regular (j : Fin 3) :
    TwoSidedRegularOn (ellipticRegularPart L j) (ellipticRegularPartDomain L) :=
  ellipticJetSum_regular L _ j []

/-- E1's termwise differentiation theorem applies at zero after its singular summand is removed. -/
theorem ellipticRegularPart_iteratedPartial (j : Fin 3) (l : List (Fin 4)) :
    iteratedPartial l (ellipticRegularPart L j) 0 =
      ∑' a : {a : L // a ≠ 0}, regularizedJet j l (a.1 : ℍ) 0 := by
  exact iteratedPartial_of_jets (ellipticJetSum L {a | a ≠ 0} j)
    (isOpen_ellipticRegularPartDomain L) (ellipticJetSum_calculus L _ j).2 l
    (zero_mem_ellipticRegularPartDomain L)

/-- The coefficient in N1 is an absolutely convergent sum, since its order is at least two. -/
theorem N1_coefficient_summable (μ : Fin 3 → ℕ) (hμ : 1 ≤ ∑ i, μ i) (j : Fin 3) :
    Summable (fun a : {a : L // a ≠ 0} => ‖higherKernel (μ + Pi.single j 1) (a.1 : ℍ)‖) := by
  apply summable_norm_eisenstein
  rw [sum_spatial_add_single]
  omega

/-- The coefficient identity for the explicit smooth remainder, at every positive spatial order. -/
theorem ellipticRegularPart_coefficient (μ : Fin 3 → ℕ) (hμ : 1 ≤ ∑ i, μ i) (j : Fin 3) :
    multiIndexPartial (spatialMultiIndex μ) (ellipticRegularPart L j) 0 =
      eisensteinCoefficient L (μ + Pi.single j 1) := by
  have hl : spatialDerivativeList μ ≠ [] := by
    intro h
    have := spatialDerivativeList_length μ
    rw [h] at this
    simp only [List.length_nil] at this
    omega
  rw [multiIndexPartial_spatial, ellipticRegularPart_iteratedPartial]
  unfold eisensteinCoefficient
  apply tsum_congr
  intro a
  simp only [regularizedJet, hl, false_and, ↓reduceIte, sub_zero, zero_add]
  exact kernelJet_spatial μ j (by simpa using a.2)

/-- Any continuous extension of `wp-G_j` agrees with the canonical remainder on a neighborhood
of zero. This makes the coefficients independent of the choice of smooth extension. -/
theorem ellipticRegularPart_extension_eqOn (j : Fin 3) {U : Set ℍ} (hU : IsOpen U)
    (h0 : (0 : ℍ) ∈ U) {h : ℍ → ℍ} (hh : ContinuousOn h U)
    (he : ∀ q ∈ U, q ∉ L → h q = elliptic L j q - kernelSpatialPartial j q) :
    Set.EqOn h (ellipticRegularPart L j) (U ∩ ellipticRegularPartDomain L) := by
  have hD := isOpen_ellipticRegularPartDomain L
  have hD0 := zero_mem_ellipticRegularPartDomain L
  have hoff (q : ℍ) (hq : q ∈ U ∩ ellipticRegularPartDomain L) (hq0 : q ≠ 0) :
      h q = ellipticRegularPart L j q := by
    rw [ellipticRegularPart_eq_sub]
    exact he q hq.1 (not_mem_lattice_of_mem_regularPartDomain L hq.2 hq0)
  have hev : h =ᶠ[𝓝[≠] (0 : ℍ)] ellipticRegularPart L j := by
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds (hU.mem_nhds h0),
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (hD.mem_nhds hD0),
      self_mem_nhdsWithin] with q hqU hqD hq0
    exact hoff q ⟨hqU, hqD⟩ hq0
  have hz : h 0 = ellipticRegularPart L j 0 :=
    tendsto_nhds_unique_of_eventuallyEq
      ((hh.continuousAt (hU.mem_nhds h0)).mono_left nhdsWithin_le_nhds)
      ((((ellipticRegularPart_regular L j).1.contDiffAt (hD.mem_nhds hD0)).continuousAt).mono_left
        nhdsWithin_le_nhds) hev
  intro q hq
  by_cases hq0 : q = 0
  · simpa [hq0] using hz
  · exact hoff q hq hq0

/-- N1 version 2, for any smooth extension near zero supplied by E1.
`Pi.single j 1` is the unit spatial multi-index; there is no factorial normalization. -/
theorem N1_v2 (j : Fin 3) {U : Set ℍ} (hU : IsOpen U) (h0 : (0 : ℍ) ∈ U)
    {h : ℍ → ℍ} (hh : ContDiffOn ℝ ∞ h U)
    (he : ∀ q ∈ U, q ∉ L → h q = elliptic L j q - kernelSpatialPartial j q)
    (μ : Fin 3 → ℕ) (hμ : 1 ≤ ∑ i, μ i) :
    multiIndexPartial (spatialMultiIndex μ) h 0 =
      eisensteinCoefficient L (μ + Pi.single j 1) := by
  have heq := ellipticRegularPart_extension_eqOn L j hU h0 hh.continuousOn he
  rw [multiIndexPartial_spatial]
  rw [iteratedPartial_congr_on (hU.inter (isOpen_ellipticRegularPartDomain L)) heq
    (spatialDerivativeList μ) ⟨h0, zero_mem_ellipticRegularPartDomain L⟩]
  rw [← multiIndexPartial_spatial]
  exact ellipticRegularPart_coefficient L μ hμ j

end MathResearch.Fueter
