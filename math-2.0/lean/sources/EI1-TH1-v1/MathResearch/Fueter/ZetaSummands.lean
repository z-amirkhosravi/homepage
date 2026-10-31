module

public import MathResearch.Fueter.EllipticPeriodicity

/-! The intact first-order Taylor remainders in E-C2 and their real derivatives. -/
@[expose] public section
noncomputable section
open scoped Quaternion Topology BigOperators ContDiff
open Filter
namespace MathResearch.Fueter
attribute [local instance] Classical.propDecidable

/-- The differentiated E-C2 summand. The zero lattice index is the leading kernel.
At order zero subtract the affine Taylor polynomial; at order one subtract its
constant derivative; at higher orders the subtraction vanishes. -/
def zetaJet (l : List (Fin 4)) (a q : ℍ) : ℍ := by
  classical
  exact iteratedPartial l kernel (q + a) - if a = 0 then 0 else
    match l with
    | [] => kernel a + fderiv ℝ kernel a q
    | [μ] => coordPartial μ kernel a
    | _ :: _ :: _ => 0

@[simp] theorem zetaJet_zero (l : List (Fin 4)) (q : ℍ) :
    zetaJet l 0 q = iteratedPartial l kernel q := by simp [zetaJet]

theorem zetaJet_nil (a q : ℍ) (ha : a ≠ 0) :
    zetaJet [] a q = kernel (q + a) - kernel a - fderiv ℝ kernel a q := by
  simp only [zetaJet, ite_eq_right ha, iteratedPartial]
  abel

@[simp] theorem zetaJet_cons_cons (μ ν : Fin 4) (l : List (Fin 4)) (a q : ℍ) :
    zetaJet (μ :: ν :: l) a q = iteratedPartial (μ :: ν :: l) kernel (q + a) := by
  simp [zetaJet]

theorem zetaJet_hasFDerivAt (l : List (Fin 4)) (a q : ℍ) (hq : q + a ≠ 0) :
    HasFDerivAt (zetaJet l a)
      (fderiv ℝ (iteratedPartial l kernel) (q + a) -
        if l = [] ∧ a ≠ 0 then fderiv ℝ kernel a else 0) q := by
  classical
  have h := (((kernel_iteratedPartial_regular l).1.contDiffAt
    (isOpen_punctured.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt.comp q
      ((hasFDerivAt_id q).add_const a)
  unfold zetaJet
  by_cases ha : a = 0
  · simpa [ha, Function.comp_def] using h
  · cases l with
    | nil =>
      simp only [ha, ite_false, iteratedPartial, ne_eq, not_false_eq_true, and_self, ite_true]
      convert! h.sub (((fderiv ℝ kernel a).hasFDerivAt).const_add (kernel a)) using 1
    | cons μ l =>
      cases l with
      | nil => simpa [ha, Function.comp_def] using h.sub_const (coordPartial μ kernel a)
      | cons ν l => simpa [ha, Function.comp_def] using h

theorem zetaJet_partial (l : List (Fin 4)) (μ : Fin 4) (a q : ℍ)
    (hq : q + a ≠ 0) :
    coordPartial μ (zetaJet l a) q = zetaJet (μ :: l) a q := by
  classical
  simp only [coordPartial, directional, (zetaJet_hasFDerivAt l a q hq).fderiv]
  cases l with
  | nil => by_cases ha : a = 0 <;> simp [zetaJet, ha, iteratedPartial, coordPartial, directional]
  | cons ν l => cases l <;> simp [zetaJet, iteratedPartial, coordPartial, directional]

theorem zetaJet_spatial (j : Fin 3) (a q : ℍ) :
    zetaJet [j.succ] a q = regularizedJet j [] a q := by
  classical
  by_cases ha : a = 0 <;> simp [zetaJet, regularizedJet, kernelJet, kernelSpatialPartial, ha, iteratedPartial]

/-- The coordinate presentation of the real differential used in E-C2. -/
theorem kernel_differential_coordinates (a q : ℍ) :
    fderiv ℝ kernel a q = ∑ μ : Fin 4, coordinateBasis.repr q μ • coordPartial μ kernel a := by
  conv_lhs => rw [← coordinateBasis.sum_repr q, map_sum]
  simp only [map_smul, coordPartial, directional]

/-- F2 also controls the operator norm of every differentiated kernel. -/
theorem kernel_iteratedPartial_fderiv_norm_le (l : List (Fin 4)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ≠ 0,
      ‖fderiv ℝ (iteratedPartial l kernel) q‖ ≤ C * ‖q‖⁻¹ ^ (4 + l.length) := by
  choose C hC hb using fun μ => kernel_iteratedPartial_norm_le (μ :: l)
  have hsum : 0 ≤ ∑ μ, C μ := Finset.sum_nonneg fun μ _ => hC μ
  let B : ℝ := Fintype.card (Fin 4) • ‖coordinateBasis.equivFunL.toContinuousLinearMap‖
  refine ⟨B * ∑ μ, C μ, by dsimp [B]; positivity, ?_⟩
  intro q hq
  have h := coordinateBasis.opNorm_le
    (u := fderiv ℝ (iteratedPartial l kernel) q)
    (M := (∑ μ, C μ) * ‖q‖⁻¹ ^ (4 + l.length)) (by positivity) ?_
  · simpa [B, mul_assoc] using h
  intro μ
  calc
    _ ≤ C μ * ‖q‖⁻¹ ^ (4 + l.length) := by
      simpa [iteratedPartial, coordPartial, directional, inv_pow,
        show 3 + (l.length + 1) = 4 + l.length by omega] using hb μ q hq
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun ν _ => hC ν) (Finset.mem_univ μ)) (by positivity)

end MathResearch.Fueter
