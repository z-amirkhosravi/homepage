module

public import MathResearch.Fueter.Elliptic
public import Mathlib.Data.List.Perm.Basic

/-! Reordering smooth real coordinate derivatives and the spatial multi-index convention. -/
@[expose] public section
noncomputable section
open scoped Quaternion Topology BigOperators ContDiff
open Filter
namespace MathResearch.Fueter

theorem contDiffOn_iteratedPartial {U : Set ℍ} (hU : IsOpen U) {f : ℍ → ℍ}
    (hf : ContDiffOn ℝ ∞ f U) (l : List (Fin 4)) :
    ContDiffOn ℝ ∞ (iteratedPartial l f) U := by
  induction l with
  | nil => exact hf
  | cons μ l ih => exact contDiffOn_directional hU ih (coordinateBasis μ)

/-- Equality on an open set is preserved by every ordered real derivative. -/
theorem iteratedPartial_congr_on {U : Set ℍ} (hU : IsOpen U) {f g : ℍ → ℍ}
    (hfg : Set.EqOn f g U) (l : List (Fin 4)) :
    Set.EqOn (iteratedPartial l f) (iteratedPartial l g) U := by
  induction l with
  | nil => exact hfg
  | cons μ l ih =>
    intro q hq
    have he : iteratedPartial l f =ᶠ[𝓝 q] iteratedPartial l g :=
      eventually_of_mem (hU.mem_nhds hq) ih
    exact congrArg (fun A : ℍ →L[ℝ] ℍ => A (coordinateBasis μ)) he.fderiv_eq

/-- Mathlib's symmetry of the second Fréchet derivative gives commuting coordinate partials. -/
theorem coordPartial_comm {U : Set ℍ} (hU : IsOpen U) {f : ℍ → ℍ}
    (hf : ContDiffOn ℝ ∞ f U) (μ ν : Fin 4) {q : ℍ} (hq : q ∈ U) :
    coordPartial μ (coordPartial ν f) q = coordPartial ν (coordPartial μ f) q := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) q :=
    ((hf.fderiv_of_isOpen (m := ∞) hU (by simp)).contDiffAt
      (hU.mem_nhds hq)).differentiableAt (by simp)
  change fderiv ℝ (directional (coordinateBasis ν) f) q (coordinateBasis μ) =
    fderiv ℝ (directional (coordinateBasis μ) f) q (coordinateBasis ν)
  rw [fderiv_directional hd, fderiv_directional hd]
  exact ((hf.contDiffAt (hU.mem_nhds hq)).isSymmSndFDerivAt (by simp)).eq _ _

/-- All reorderings of an ordered derivative list agree on the smooth open domain. -/
theorem iteratedPartial_perm {U : Set ℍ} (hU : IsOpen U) {f : ℍ → ℍ}
    (hf : ContDiffOn ℝ ∞ f U) {l m : List (Fin 4)} (hp : l.Perm m) :
    Set.EqOn (iteratedPartial l f) (iteratedPartial m f) U := by
  induction hp with
  | nil => exact fun _ _ => rfl
  | cons μ _ ih => exact iteratedPartial_congr_on hU ih [μ]
  | swap μ ν l =>
    intro q hq
    exact coordPartial_comm hU (contDiffOn_iteratedPartial hU hf l) ν μ hq
  | trans _ _ ih₁ ih₂ => exact fun _ hq => (ih₁ hq).trans (ih₂ hq)

/-- The ordered list implementing `∂₁^μ₁ ∂₂^μ₂ ∂₃^μ₃`. -/
def spatialDerivativeList (μ : Fin 3 → ℕ) : List (Fin 4) :=
  List.replicate (μ 0) 1 ++ List.replicate (μ 1) 2 ++ List.replicate (μ 2) 3

theorem multiIndexPartial_spatial (μ : Fin 3 → ℕ) (f : ℍ → ℍ) :
    multiIndexPartial (spatialMultiIndex μ) f = iteratedPartial (spatialDerivativeList μ) f := by
  rfl

theorem spatialDerivativeList_length (μ : Fin 3 → ℕ) :
    (spatialDerivativeList μ).length = ∑ i, μ i := by
  simp [spatialDerivativeList, Fin.sum_univ_succ]

/-- Adding a unit multi-index inserts exactly one derivative in the corresponding coordinate. -/
theorem spatialDerivativeList_add_single (μ : Fin 3 → ℕ) (j : Fin 3) :
    (spatialDerivativeList μ ++ [j.succ]).Perm (spatialDerivativeList (μ + Pi.single j 1)) := by
  apply List.perm_iff_count.mpr
  intro i
  fin_cases i <;> fin_cases j <;>
    simp [spatialDerivativeList, List.count_append, List.count_replicate, Pi.add_apply,
      Nat.add_comm]

/-- The derivative occurring in E1 is exactly the higher kernel indexed in N1. -/
theorem kernelJet_spatial (μ : Fin 3 → ℕ) (j : Fin 3) {q : ℍ} (hq : q ≠ 0) :
    kernelJet j (spatialDerivativeList μ) q = higherKernel (μ + Pi.single j 1) q := by
  rw [higherKernel, multiIndexPartial_spatial]
  exact iteratedPartial_perm isOpen_punctured kernel_smooth
    (spatialDerivativeList_add_single μ j) hq

end MathResearch.Fueter
