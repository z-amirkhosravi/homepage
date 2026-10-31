module
public import MathResearch.Fueter.Zeta

/-! E3: oddness, both regularity equations, real derivatives, and additive quasiperiods. -/
@[expose] public section
noncomputable section
open scoped Quaternion Topology BigOperators ContDiff
open Filter
namespace MathResearch.Fueter

/-- Differentiating the odd kernel gives an even real differential. -/
theorem kernel_fderiv_neg (a : ℍ) (ha : a ≠ 0) :
    fderiv ℝ kernel (-a) = fderiv ℝ kernel a := by
  apply ContinuousLinearMap.ext
  intro v
  rw [kernel_differential_coordinates, kernel_differential_coordinates]
  apply Finset.sum_congr rfl
  intro μ _
  congr 1
  simpa [iteratedPartial] using kernel_iteratedPartial_neg [μ] a ha

/-- Oddness reindexes the entire Taylor brackets, without separating divergent series. -/
theorem zeta_odd (L : Submodule ℤ ℍ) : Function.Odd (zeta L) := by
  intro q
  unfold zeta
  rw [kernel_odd, neg_add, ← tsum_neg, ← (nonzeroLatticeNeg L).tsum_eq]
  congr 1
  apply tsum_congr
  intro a
  have ha : (a.1 : ℍ) ≠ 0 := by simpa using a.2
  change kernel (-q + -(a.1 : ℍ)) - kernel (-(a.1 : ℍ)) -
    fderiv ℝ kernel (-(a.1 : ℍ)) (-q) = _
  rw [← neg_add, kernel_odd, kernel_odd, kernel_fderiv_neg _ ha, map_neg]
  abel

variable (L : Submodule ℤ ℍ) [DiscreteTopology L] [IsZLattice ℝ L]

/-- Left regularity determines the time derivative from the three E-C1 functions. -/
theorem zeta_timePartial {q : ℍ} (hq : q ∉ L) :
    coordPartial 0 (zeta L) q = -∑ j : Fin 3, coordinateBasis j.succ * elliptic L j q := by
  have h := (zeta_regular L).2.1 q hq
  rw [leftOperator_eq, Fin.sum_univ_succ] at h
  have h0 : coordinateBasis 0 = 1 := by rw [coordinateBasis_eq]; rfl
  simp only [h0, one_mul, zeta_spatialPartial L _ hq] at h
  exact eq_neg_of_add_eq_zero_left h

theorem zeta_coordPartial_add (μ : Fin 4) (w : L) {q : ℍ} (hq : q ∉ L) :
    coordPartial μ (zeta L) (q + (w : ℍ)) = coordPartial μ (zeta L) q := by
  refine Fin.cases ?_ (fun j => ?_) μ
  · rw [zeta_timePartial L (not_mem_lattice_add L w hq), zeta_timePartial L hq]
    simp only [elliptic_add L _ w hq]
  · rw [zeta_spatialPartial L j (not_mem_lattice_add L w hq),
      zeta_spatialPartial L j hq, elliptic_add L j w hq]

theorem zeta_fderiv_add (w : L) {q : ℍ} (hq : q ∉ L) :
    fderiv ℝ (zeta L) (q + (w : ℍ)) = fderiv ℝ (zeta L) q := by
  apply ContinuousLinearMap.ext
  intro v
  rw [← coordinateBasis.sum_repr v]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro μ _
  congr 1
  exact zeta_coordPartial_add L μ w hq

/-- The increment is constant on the connected complement of the lattice. -/
theorem zeta_increment_const (w : L) {q r : ℍ} (hq : q ∉ L) (hr : r ∉ L) :
    zeta L (q + (w : ℍ)) - zeta L q = zeta L (r + (w : ℍ)) - zeta L r := by
  let H : ℍ → ℍ := fun x => zeta L (x + (w : ℍ)) - zeta L x
  have hU := (isClosed_quaternionLattice L).isOpen_compl
  have hd (x) (hx : x ∉ L) : DifferentiableAt ℝ (zeta L) x :=
    ((zeta_regular L).1.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hH (x) (hx : x ∉ L) : HasFDerivAt (𝕜 := ℝ) H 0 x := by
    have h := ((hd _ (not_mem_lattice_add L w hx)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).add_const (w : ℍ))).sub (hd x hx).hasFDerivAt
    convert! h using 1
    simp [zeta_fderiv_add L w hx]
  exact hU.is_const_of_fderiv_eq_zero (isConnected_lattice_compl L).isPreconnected
    (fun x hx => (hH x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hH x hx).fderiv) hq hr

/-- A basepoint only constructs the map; `zeta_increment_const` proves independence. -/
def zetaBasepoint : ℍ := (isConnected_lattice_compl L).nonempty.choose

omit [IsZLattice ℝ L] in
theorem zetaBasepoint_not_mem : zetaBasepoint L ∉ L :=
  (isConnected_lattice_compl L).nonempty.choose_spec

/-- The additive quasiperiod map η_L : L → ℍ. -/
def zetaQuasiperiod : L →+ ℍ where
  toFun w := zeta L (zetaBasepoint L + (w : ℍ)) - zeta L (zetaBasepoint L)
  map_zero' := by simp
  map_add' v w := by
    have h := zeta_increment_const L w (not_mem_lattice_add L v (zetaBasepoint_not_mem L))
      (zetaBasepoint_not_mem L)
    change zeta L (zetaBasepoint L + ((v : ℍ) + (w : ℍ))) - zeta L (zetaBasepoint L) = _
    rw [sub_eq_iff_eq_add] at h
    rw [← add_assoc, h]
    abel

/-- The quasiperiod identity holds at every off-lattice point. -/
theorem zeta_add (w : L) {q : ℍ} (hq : q ∉ L) :
    zeta L (q + (w : ℍ)) - zeta L q = zetaQuasiperiod L w :=
  zeta_increment_const L w hq (zetaBasepoint_not_mem L)

theorem zeta_unique_quasiperiod :
    ∃! η : L →+ ℍ, ∀ w : L, ∀ q : ℍ, q ∉ L →
      zeta L (q + (w : ℍ)) - zeta L q = η w := by
  refine ⟨zetaQuasiperiod L, fun w _ hq => zeta_add L w hq, ?_⟩
  intro η hη
  apply AddMonoidHom.ext
  intro w
  exact (hη w (zetaBasepoint L) (zetaBasepoint_not_mem L)).symm

/-- E3 version 2. Index zero is the leading kernel; every nonzero index is exactly
E-C2's intact Taylor bracket. Lists include time and all orders of real differentiation. -/
theorem E3_v2 :
    (∀ l : List (Fin 4), ∀ q ∉ L,
      Summable (fun a : L => ‖iteratedPartial l (zetaJet [] (a : ℍ)) q‖)) ∧
    (∀ l : List (Fin 4), ∀ K : Set ℍ, IsCompact K → K ⊆ (L : Set ℍ)ᶜ →
      TendstoUniformlyOn (fun s : Finset L => fun q =>
        ∑ a ∈ s, iteratedPartial l (zetaJet [] (a : ℍ)) q)
        (iteratedPartial l (zeta L)) atTop K) ∧
    (∀ l : List (Fin 4), HasSumLocallyUniformlyOn
      (fun a : L => iteratedPartial l (zetaJet [] (a : ℍ)))
      (iteratedPartial l (zeta L)) (L : Set ℍ)ᶜ) ∧
    Function.Odd (zeta L) ∧
    TwoSidedRegularOn (zeta L) (L : Set ℍ)ᶜ ∧
    (∀ j : Fin 3, ∀ q ∉ L, coordPartial j.succ (zeta L) q = elliptic L j q) ∧
    (∃! η : L →+ ℍ, ∀ w : L, ∀ q : ℍ, q ∉ L →
      zeta L (q + (w : ℍ)) - zeta L q = η w) := by
  exact ⟨fun l _ hq => (zeta_termwise_normal L l).summable_norm hq,
    fun l _ hK hKL => zeta_termwise_uniformOn L l hK hKL,
    zeta_termwise_locallyUniform L, zeta_odd L, zeta_regular L,
    fun j _ hq => zeta_spatialPartial L j hq, zeta_unique_quasiperiod L⟩

end MathResearch.Fueter
