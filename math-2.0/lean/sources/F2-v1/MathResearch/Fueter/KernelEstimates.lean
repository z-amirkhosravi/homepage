module

public import MathResearch.Fueter.Kernel
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.ProperSpace

/-! F2: homogeneity, parity and derivative bounds for the Cauchy–Fueter kernel. -/

@[expose] public section
noncomputable section
open scoped Quaternion Topology BigOperators ContDiff

namespace MathResearch.Fueter

/-- The kernel has degree `-3` under every nonzero real dilation. -/
theorem kernel_smul (a : ℝ) (ha : a ≠ 0) (q : ℍ) :
    kernel (a • q) = (a ^ 3)⁻¹ • kernel q := by
  simp only [kernel, Quaternion.normSq_smul, Quaternion.star_smul, smul_smul]
  congr 1
  field_simp

/-- Differentiating a dilation identity reduces the degree by one. The identity
is required only off zero, and differentiability is explicit on that open set. -/
theorem directional_smul_of_eq {f : ℍ → ℍ} (hf : ContDiffOn ℝ ∞ f punctured)
    {a c : ℝ} (ha : a ≠ 0) (h : ∀ q ≠ 0, f (a • q) = c • f q)
    {q : ℍ} (hq : q ≠ 0) (v : ℍ) :
    directional v f (a • q) = (a⁻¹ * c) • directional v f q := by
  have hd (x : ℍ) (hx : x ≠ 0) : DifferentiableAt ℝ f x :=
    (hf.contDiffAt (isOpen_punctured.mem_nhds hx)).differentiableAt (by simp)
  have heq : (fun x => f (a • x)) =ᶠ[𝓝 q] fun x => c • f x :=
    Filter.eventually_of_mem (isOpen_punctured.mem_nhds hq) fun x hx => h x hx
  have hl := (hd (a • q) (smul_ne_zero ha hq)).hasFDerivAt.comp q
    ((hasFDerivAt_id q).const_smul a)
  have hr := (hd q hq).hasFDerivAt.const_smul c
  have he := congrArg (fun L : ℍ →L[ℝ] ℍ => L v)
    (hl.fderiv.symm.trans (heq.fderiv_eq.trans hr.fderiv))
  have he' : a • directional v f (a • q) = c • directional v f q := by
    simpa [directional] using he
  have := congrArg (fun z : ℍ => a⁻¹ • z) he'
  simpa [smul_smul, ha] using this

/-- All ordered real derivatives have the expected negative degree. -/
theorem kernel_iteratedPartial_smul (l : List (Fin 4)) (a : ℝ) (ha : a ≠ 0)
    (q : ℍ) (hq : q ≠ 0) :
    iteratedPartial l kernel (a • q) =
      (a ^ (3 + l.length))⁻¹ • iteratedPartial l kernel q := by
  induction l generalizing q with
  | nil => exact kernel_smul a ha q
  | cons μ l ih =>
    change directional (coordinateBasis μ) (iteratedPartial l kernel) (a • q) = _
    rw [directional_smul_of_eq (kernel_iteratedPartial_regular l).1 ha ih hq]
    change (a⁻¹ * (a ^ (3 + l.length))⁻¹) •
        directional (coordinateBasis μ) (iteratedPartial l kernel) q =
      (a ^ (3 + (l.length + 1)))⁻¹ •
        directional (coordinateBasis μ) (iteratedPartial l kernel) q
    rw [← Nat.add_assoc, pow_succ, mul_inv_rev]

/-- Parity holds for every ordering of real coordinate derivatives. -/
theorem kernel_iteratedPartial_neg (l : List (Fin 4)) (q : ℍ) (hq : q ≠ 0) :
    iteratedPartial l kernel (-q) =
      (-1 : ℝ) ^ (l.length + 1) • iteratedPartial l kernel q := by
  have hc : ((-1 : ℝ) ^ (3 + l.length))⁻¹ = (-1 : ℝ) ^ (l.length + 1) := by
    rw [← inv_pow]
    norm_num [pow_add, mul_comm]
  have h := kernel_iteratedPartial_smul l (-1) (by norm_num) q hq
  rw [neg_one_smul, hc] at h
  exact h

private theorem partial_list_length (α : Fin 4 → ℕ) :
    (List.replicate (α 0) (0 : Fin 4) ++ List.replicate (α 1) 1 ++
      List.replicate (α 2) 2 ++ List.replicate (α 3) 3).length = ∑ μ, α μ := by
  simp [List.length_append, List.length_replicate, Fin.sum_univ_succ]

/-- The multi-index homogeneity formula in F2. -/
theorem kernel_multiIndexPartial_smul (α : Fin 4 → ℕ) (a : ℝ) (ha : a ≠ 0)
    (q : ℍ) (hq : q ≠ 0) :
    multiIndexPartial α kernel (a • q) =
      (a ^ (3 + ∑ μ, α μ))⁻¹ • multiIndexPartial α kernel q := by
  unfold multiIndexPartial
  rw [← partial_list_length α]
  exact kernel_iteratedPartial_smul
      (List.replicate (α 0) 0 ++ List.replicate (α 1) 1 ++
        List.replicate (α 2) 2 ++ List.replicate (α 3) 3) a ha q hq

/-- The multi-index parity formula in F2. -/
theorem kernel_multiIndexPartial_neg (α : Fin 4 → ℕ) (q : ℍ) (hq : q ≠ 0) :
    multiIndexPartial α kernel (-q) =
      (-1 : ℝ) ^ ((∑ μ, α μ) + 1) • multiIndexPartial α kernel q := by
  unfold multiIndexPartial
  rw [← partial_list_length α]
  exact kernel_iteratedPartial_neg
      (List.replicate (α 0) 0 ++ List.replicate (α 1) 1 ++
        List.replicate (α 2) 2 ++ List.replicate (α 3) 3) q hq

/-- Compactness of the unit sphere turns homogeneity into the global decay bound. -/
theorem kernel_iteratedPartial_norm_le (l : List (Fin 4)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℍ, q ≠ 0 →
      ‖iteratedPartial l kernel q‖ ≤ C * (‖q‖ ^ (3 + l.length))⁻¹ := by
  have hs : Metric.sphere (0 : ℍ) 1 ⊆ punctured := by
    intro q hq
    have hn : ‖q‖ = 1 := by simpa using hq
    exact norm_ne_zero_iff.mp (by rw [hn]; norm_num)
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : ℍ) 1).exists_bound_of_continuousOn
    ((kernel_iteratedPartial_regular l).1.continuousOn.mono hs)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro q hq
  let u : ℍ := ‖q‖⁻¹ • q
  have hn : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, ne_of_gt hn]
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; norm_num)
  have hqu : ‖q‖ • u = q := by simp [u, smul_smul, ne_of_gt hn]
  have hscale := kernel_iteratedPartial_smul l ‖q‖ (ne_of_gt hn) u hu0
  rw [hqu] at hscale
  rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hbound : ‖iteratedPartial l kernel u‖ ≤ max C 0 :=
    (hC u (by simpa using hu)).trans (le_max_left _ _)
  calc
    (‖q‖ ^ (3 + l.length))⁻¹ * ‖iteratedPartial l kernel u‖ ≤
        (‖q‖ ^ (3 + l.length))⁻¹ * max C 0 := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = max C 0 * (‖q‖ ^ (3 + l.length))⁻¹ := mul_comm _ _

/-- The derivative bound in F2, with a nonnegative constant depending only on `α`. -/
theorem kernel_multiIndexPartial_norm_le (α : Fin 4 → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℍ, q ≠ 0 →
      ‖multiIndexPartial α kernel q‖ ≤ C * (‖q‖ ^ (3 + ∑ μ, α μ))⁻¹ := by
  unfold multiIndexPartial
  rw [← partial_list_length α]
  exact kernel_iteratedPartial_norm_le
      (List.replicate (α 0) 0 ++ List.replicate (α 1) 1 ++
        List.replicate (α 2) 2 ++ List.replicate (α 3) 3)

/-- The coordinate of `q` in F-D1 is its real inner product with that basis vector. -/
theorem inner_coordinateBasis (q : ℍ) (μ : Fin 4) :
    inner ℝ q (coordinateBasis μ) = coordinateBasis.repr q μ := by
  rw [coordinateBasis_eq]
  simp only [coordinateBasis, QuaternionAlgebra.coe_basisOneIJK_repr]
  fin_cases μ <;> simp [Quaternion.inner_def]

/-- Conjugation negates each of the three spatial basis vectors. -/
theorem star_spatial_basis (j : Fin 3) :
    star (coordinateBasis j.succ) = -coordinateBasis j.succ := by
  fin_cases j <;> ext <;> simp [coordinateBasis_eq]

/-- The three functions `G_j` in F-D3; Lean indices `0,1,2` mean `x₁,x₂,x₃`. -/
def kernelSpatialPartial (j : Fin 3) : ℍ → ℍ := coordPartial j.succ kernel

/-- F2's explicit first spatial derivative, with the coordinate and order fixed. -/
theorem kernelSpatialPartial_eq (j : Fin 3) (q : ℍ) (hq : q ≠ 0) :
    kernelSpatialPartial j q =
      -(‖q‖ ^ 4)⁻¹ • coordinateBasis j.succ -
        (4 * coordinateBasis.repr q j.succ * (‖q‖ ^ 6)⁻¹) • star q := by
  unfold kernelSpatialPartial coordPartial directional
  rw [fderiv_kernel hq, inner_coordinateBasis, star_spatial_basis]
  simp only [Quaternion.normSq_eq_norm_mul_self, ← pow_two, ← inv_pow, ← pow_mul]
  simp only [smul_neg, neg_smul]
  congr 1
  congr 1
  ring

/-- Oddness of the ambient total kernel, including its zero value at zero. -/
theorem kernel_odd : Function.Odd kernel := by
  intro q
  have h := kernel_smul (-1) (by norm_num) q
  norm_num at h
  exact h

/-- Each first spatial derivative is even off its pole. -/
theorem kernelSpatialPartial_even (j : Fin 3) (q : ℍ) (hq : q ≠ 0) :
    kernelSpatialPartial j (-q) = kernelSpatialPartial j q := by
  have h := kernel_iteratedPartial_neg [j.succ] q hq
  simpa [kernelSpatialPartial, iteratedPartial] using h

/-- F2 version 1: all real multi-indices, a constant independent of `q` and `a`,
and the three stated consequences. Reciprocal natural powers express the
negative integral exponents in the written statement. -/
theorem F2_v1 :
    (∀ α : Fin 4 → ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℍ, q ≠ 0 → ∀ a : ℝ, 0 < a →
      multiIndexPartial α kernel (a • q) =
          (a ^ (3 + ∑ μ, α μ))⁻¹ • multiIndexPartial α kernel q ∧
      multiIndexPartial α kernel (-q) =
          (-1 : ℝ) ^ ((∑ μ, α μ) + 1) • multiIndexPartial α kernel q ∧
      ‖multiIndexPartial α kernel q‖ ≤ C * (‖q‖ ^ (3 + ∑ μ, α μ))⁻¹) ∧
    Function.Odd kernel ∧
    (∀ j : Fin 3, ∀ q : ℍ, q ≠ 0 →
      kernelSpatialPartial j (-q) = kernelSpatialPartial j q) ∧
    (∀ j : Fin 3, ∀ q : ℍ, q ≠ 0 →
      kernelSpatialPartial j q =
        -(‖q‖ ^ 4)⁻¹ • coordinateBasis j.succ -
          (4 * coordinateBasis.repr q j.succ * (‖q‖ ^ 6)⁻¹) • star q) := by
  refine ⟨?_, kernel_odd, kernelSpatialPartial_even, kernelSpatialPartial_eq⟩
  intro α
  obtain ⟨C, hC, hbound⟩ := kernel_multiIndexPartial_norm_le α
  exact ⟨C, hC, fun q hq a ha =>
    ⟨kernel_multiIndexPartial_smul α a (ne_of_gt ha) q hq,
      kernel_multiIndexPartial_neg α q hq, hbound q hq⟩⟩

end MathResearch.Fueter
