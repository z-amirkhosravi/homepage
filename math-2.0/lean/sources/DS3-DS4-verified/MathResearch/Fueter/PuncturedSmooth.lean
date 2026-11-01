module
public import MathResearch.Fueter.QuaternionRotations
public import MathResearch.Fueter.PartialCommutation

/-! Smooth quaternion-valued functions off zero, with a fixed zero extension.
Right quaternion scalars use mathlib's opposite-ring module convention. -/
@[expose] public section
noncomputable section
open scoped Quaternion Topology BigOperators ContDiff
open Filter
namespace MathResearch.Fueter

/-- The zero extension makes equality of punctured functions ordinary equality. -/
def smoothPuncturedSpace : Submodule ℍᵐᵒᵖ (ℍ → ℍ) where
  carrier := {f | ContDiffOn ℝ ∞ f punctured ∧ f 0 = 0}
  zero_mem' := ⟨contDiffOn_const, rfl⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, by simp only [Pi.add_apply, hf.2, hg.2, add_zero]⟩
  smul_mem' c f hf := by
    refine ⟨?_, ?_⟩
    · change ContDiffOn ℝ ∞ (fun q => f q * c.unop) punctured
      exact hf.1.mul contDiffOn_const
    · change f 0 * c.unop = 0
      rw [hf.2, zero_mul]

abbrev SmoothPunctured : Type := smoothPuncturedSpace

instance : CoeFun SmoothPunctured (fun _ => ℍ → ℍ) := ⟨Subtype.val⟩

@[simp] theorem smoothPunctured_add_apply (f g : SmoothPunctured) (q : ℍ) :
    (f + g) q = f q + g q := rfl
@[simp] theorem smoothPunctured_smul_apply (c : ℍᵐᵒᵖ) (f : SmoothPunctured) (q : ℍ) :
    (c • f) q = f q * c.unop := rfl
@[simp] theorem smoothPunctured_neg_apply (f : SmoothPunctured) (q : ℍ) :
    (-f) q = -f q := rfl
@[simp] theorem smoothPunctured_sum_apply {ι : Type*} (s : Finset ι)
    (f : ι → SmoothPunctured) (q : ℍ) : (∑ i ∈ s, f i) q = ∑ i ∈ s, f i q := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih => simp only [Finset.sum_insert ha, smoothPunctured_add_apply, ih]

/-- Restrict a smooth function to the punctured domain and extend it by zero. -/
def puncturedSmooth (f : ℍ → ℍ) (hf : ContDiffOn ℝ ∞ f punctured) : SmoothPunctured := by
  classical
  exact ⟨fun q => if q = 0 then 0 else f q,
    hf.congr (fun q hq => by change q ≠ 0 at hq; simp [hq]),
    by simp⟩

@[simp] theorem puncturedSmooth_apply {f : ℍ → ℍ} {hf : ContDiffOn ℝ ∞ f punctured}
    {q : ℍ} (hq : q ≠ 0) : puncturedSmooth f hf q = f q := by simp [puncturedSmooth, hq]

@[simp] theorem smoothPunctured_zero (f : SmoothPunctured) : f 0 = 0 := f.property.2

theorem smoothPunctured_smooth (f : SmoothPunctured) : ContDiffOn ℝ ∞ f punctured := f.property.1

theorem smoothPunctured_differentiable (f : SmoothPunctured) {q : ℍ} (hq : q ≠ 0) :
    DifferentiableAt ℝ f q :=
  ((smoothPunctured_smooth f).contDiffAt (isOpen_punctured.mem_nhds hq)).differentiableAt (by simp)

theorem puncturedSmooth_fderiv {f : ℍ → ℍ} {hf : ContDiffOn ℝ ∞ f punctured}
    {q : ℍ} (hq : q ≠ 0) : fderiv ℝ (puncturedSmooth f hf) q = fderiv ℝ f q := by
  apply Filter.EventuallyEq.fderiv_eq
  exact eventually_of_mem (isOpen_punctured.mem_nhds hq) (fun _ hy => puncturedSmooth_apply hy)

@[ext] theorem SmoothPunctured.ext {f g : SmoothPunctured}
    (h : ∀ q ≠ 0, f q = g q) : f = g := by
  apply Subtype.ext
  funext q
  by_cases hq : q = 0
  · subst q; simp
  · exact h q hq

/-- Differentiation is right quaternion linear on the smooth punctured space. -/
def smoothDerivative (v : ℍ) : SmoothPunctured →ₗ[ℍᵐᵒᵖ] SmoothPunctured where
  toFun f := puncturedSmooth (directional v f)
    (contDiffOn_directional isOpen_punctured (smoothPunctured_smooth f) v)
  map_add' f g := by
    apply SmoothPunctured.ext
    intro q hq
    simp only [smoothPunctured_add_apply, puncturedSmooth_apply hq]
    change fderiv ℝ (fun x => f x + g x) q v = fderiv ℝ f q v + fderiv ℝ g q v
    rw [fderiv_fun_add (smoothPunctured_differentiable f hq) (smoothPunctured_differentiable g hq)]
    rfl
  map_smul' c f := by
    apply SmoothPunctured.ext
    intro q hq
    simp only [smoothPunctured_smul_apply, puncturedSmooth_apply hq, RingHom.id_apply]
    change fderiv ℝ (fun x => f x * c.unop) q v = fderiv ℝ f q v * c.unop
    rw [fderiv_mul_const' (smoothPunctured_differentiable f hq)]
    rfl

@[simp] theorem smoothDerivative_apply (v : ℍ) (f : SmoothPunctured) {q : ℍ} (hq : q ≠ 0) :
    smoothDerivative v f q = directional v f q := by
  exact puncturedSmooth_apply (hf := contDiffOn_directional isOpen_punctured (smoothPunctured_smooth f) v) hq

theorem higherKernel_smooth (ν : Fin 3 → ℕ) : ContDiffOn ℝ ∞ (higherKernel ν) punctured :=
  (kernel_regular.multiIndexPartial isOpen_punctured _).1

/-- The order-ν spatial derivative of the kernel, viewed on its natural domain. -/
def smoothHigherKernel (ν : Fin 3 → ℕ) : SmoothPunctured :=
  puncturedSmooth (higherKernel ν) (higherKernel_smooth ν)

/-- The right-H span in EI7; r counts spatial derivatives, not radial degree. -/
def kernelDerivativeSpace (r : ℕ) : Submodule ℍᵐᵒᵖ SmoothPunctured :=
  Submodule.span ℍᵐᵒᵖ (Set.range (fun ν : {ν : Fin 3 → ℕ // ∑ j, ν j = r} => smoothHigherKernel ν))

@[simp] theorem smoothHigherKernel_apply (ν : Fin 3 → ℕ) {q : ℍ} (hq : q ≠ 0) :
    smoothHigherKernel ν q = higherKernel ν q := puncturedSmooth_apply hq

theorem smoothHigherKernel_mem (ν : Fin 3 → ℕ) :
    smoothHigherKernel ν ∈ kernelDerivativeSpace (∑ j, ν j) :=
  Submodule.subset_span ⟨⟨ν, rfl⟩, rfl⟩

theorem smoothDerivative_spatial (ν : Fin 3 → ℕ) (j : Fin 3) :
    smoothDerivative (coordinateBasis j.succ) (smoothHigherKernel ν) =
      smoothHigherKernel (ν + Pi.single j 1) := by
  apply SmoothPunctured.ext
  intro q hq
  rw [smoothDerivative_apply _ _ hq, smoothHigherKernel_apply _ hq]
  change fderiv ℝ (puncturedSmooth (higherKernel ν) _) q (coordinateBasis j.succ) = _
  rw [puncturedSmooth_fderiv hq]
  change iteratedPartial (j.succ :: spatialDerivativeList ν) kernel q =
    iteratedPartial (spatialDerivativeList (ν + Pi.single j 1)) kernel q
  exact iteratedPartial_perm isOpen_punctured kernel_smooth
    ((List.perm_append_comm (l₁ := [j.succ]) (l₂ := spatialDerivativeList ν)).trans
      (spatialDerivativeList_add_single ν j)) hq

/-- Right regularity eliminates the time derivative, with coefficients on the right. -/
theorem smoothDerivative_time (ν : Fin 3 → ℕ) :
    smoothDerivative (coordinateBasis 0) (smoothHigherKernel ν) =
      -∑ j : Fin 3, MulOpposite.op (coordinateBasis j.succ) •
        smoothDerivative (coordinateBasis j.succ) (smoothHigherKernel ν) := by
  apply SmoothPunctured.ext
  intro q hq
  have h := (kernel_regular.multiIndexPartial isOpen_punctured (spatialMultiIndex ν)).2.2 q hq
  rw [rightOperator_eq, Fin.sum_univ_succ] at h
  have he (μ : Fin 4) : smoothDerivative (coordinateBasis μ) (smoothHigherKernel ν) q =
      coordPartial μ (higherKernel ν) q := by
    rw [smoothDerivative_apply _ _ hq]
    exact congrArg (fun A : ℍ →L[ℝ] ℍ => A (coordinateBasis μ)) (puncturedSmooth_fderiv hq)
  simp only [smoothPunctured_neg_apply, smoothPunctured_sum_apply, smoothPunctured_smul_apply]
  change _ = -(∑ j : Fin 3, (smoothDerivative (coordinateBasis j.succ) (smoothHigherKernel ν)) q *
    coordinateBasis j.succ)
  simp only [he]
  have hb : coordinateBasis 0 = 1 := coordinateBasis_eq 0
  rw [hb, mul_one] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Arbitrary real directions are finite real combinations of coordinate derivatives. -/
theorem smoothDerivative_coordinates (v : ℍ) (f : SmoothPunctured) :
    smoothDerivative v f = ∑ μ : Fin 4,
      MulOpposite.op ((coordinateBasis.repr v μ : ℝ) : ℍ) • smoothDerivative (coordinateBasis μ) f := by
  apply SmoothPunctured.ext
  intro q hq
  simp only [smoothPunctured_sum_apply, smoothPunctured_smul_apply]
  change smoothDerivative v f q = ∑ μ : Fin 4,
    smoothDerivative (coordinateBasis μ) f q * ((coordinateBasis.repr v μ : ℝ) : ℍ)
  simp only [smoothDerivative_apply _ _ hq, Quaternion.mul_coe_eq_smul, directional]
  conv_lhs => rw [← coordinateBasis.sum_repr v]
  simp only [map_sum, map_smul]

theorem smoothDerivative_mem {r : ℕ} (v : ℍ) {f : SmoothPunctured}
    (hf : f ∈ kernelDerivativeSpace r) : smoothDerivative v f ∈ kernelDerivativeSpace (r + 1) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    change x ∈ Set.range (fun ν : {ν : Fin 3 → ℕ // ∑ j, ν j = r} => smoothHigherKernel ν) at hx
    obtain ⟨⟨ν, hν⟩, rfl⟩ := hx
    have hs (j : Fin 3) : smoothDerivative (coordinateBasis j.succ) (smoothHigherKernel ν) ∈
        kernelDerivativeSpace (r + 1) := by
      rw [smoothDerivative_spatial]
      have hn : ∑ i : Fin 3, (ν + Pi.single j 1 : Fin 3 → ℕ) i = r + 1 := by
        simp only [Pi.add_apply, Finset.sum_add_distrib, hν]
        simp
      rw [← hn]
      exact smoothHigherKernel_mem _
    rw [smoothDerivative_coordinates]
    apply Submodule.sum_mem
    intro μ _
    apply Submodule.smul_mem
    refine Fin.cases ?_ (fun j => hs j) μ
    rw [smoothDerivative_time]
    apply Submodule.neg_mem
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hs j))
  | zero => simp
  | add x y _ _ hx hy => simpa using (kernelDerivativeSpace (r + 1)).add_mem hx hy
  | smul c x _ hx => simpa using (kernelDerivativeSpace (r + 1)).smul_mem c hx

end MathResearch.Fueter
