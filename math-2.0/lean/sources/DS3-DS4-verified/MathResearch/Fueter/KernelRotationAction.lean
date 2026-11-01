module
public import MathResearch.Fueter.PuncturedSmooth

/-! The spin action preserves the right quaternion span of the spatial kernel derivatives. -/
@[expose] public section
noncomputable section
open scoped Quaternion Topology BigOperators ContDiff
namespace MathResearch.Fueter

/-- `ρ(a,b) f(q) = b f(a⁻¹ q b)`, on the smooth punctured space. -/
def smoothRho (k : QuaternionSpinPair) : SmoothPunctured →ₗ[ℍᵐᵒᵖ] SmoothPunctured where
  toFun f := ⟨fun q => (k.2 : ℍ) * f (quaternionRotation k⁻¹ q), by
    constructor
    · exact contDiffOn_const.mul ((smoothPunctured_smooth f).comp
        (quaternionRotation k⁻¹).toContinuousLinearEquiv.contDiff.contDiffOn
        (fun q hq => (map_ne_zero_iff (quaternionRotation k⁻¹) (quaternionRotation k⁻¹).injective).mpr hq))
    · simp⟩
  map_add' f g := by
    apply SmoothPunctured.ext
    intro q _
    exact mul_add _ _ _
  map_smul' c f := by
    apply SmoothPunctured.ext
    intro q _
    exact (mul_assoc _ _ _).symm

@[simp] theorem smoothRho_apply (k : QuaternionSpinPair) (f : SmoothPunctured) (q : ℍ) :
    smoothRho k f q = (k.2 : ℍ) * f (quaternionRotation k⁻¹ q) := rfl

@[simp] theorem smoothRho_one : smoothRho 1 = LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply SmoothPunctured.ext
  intro q _
  simp [smoothRho_apply]

theorem smoothRho_mul (k l : QuaternionSpinPair) (f : SmoothPunctured) :
    smoothRho (k * l) f = smoothRho k (smoothRho l f) := by
  apply SmoothPunctured.ext
  intro q _
  simp [smoothRho_apply, quaternionRotation, star_mul, mul_assoc]

@[simp] theorem smoothRho_inv_cancel (k : QuaternionSpinPair) (f : SmoothPunctured) :
    smoothRho k⁻¹ (smoothRho k f) = f := by rw [← smoothRho_mul]; simp

@[simp] theorem smoothRho_cancel_inv (k : QuaternionSpinPair) (f : SmoothPunctured) :
    smoothRho k (smoothRho k⁻¹ f) = f := by rw [← smoothRho_mul]; simp

/-- Chain rule for the spin action, in an arbitrary real direction. -/
theorem smoothRho_fderiv (k : QuaternionSpinPair) (f : SmoothPunctured) {q : ℍ}
    (hq : q ≠ 0) (v : ℍ) :
    fderiv ℝ (smoothRho k f) q v =
      (k.2 : ℍ) * fderiv ℝ f (quaternionRotation k⁻¹ q) (quaternionRotation k⁻¹ v) := by
  have hq' : quaternionRotation k⁻¹ q ≠ 0 := (map_ne_zero_iff (quaternionRotation k⁻¹) (quaternionRotation k⁻¹).injective).mpr hq
  have hd : DifferentiableAt ℝ (fun x => f (quaternionRotation k⁻¹ x)) q :=
    (smoothPunctured_differentiable f hq').comp q
    (quaternionRotation k⁻¹).toContinuousLinearEquiv.differentiableAt
  change fderiv ℝ (fun q => (k.2 : ℍ) * f (quaternionRotation k⁻¹ q)) q v = _
  rw [fderiv_const_mul hd]
  change (k.2 : ℍ) * (fderiv ℝ (f ∘ quaternionRotation k⁻¹) q) v = _
  rw [fderiv_comp q (smoothPunctured_differentiable f hq')
    (quaternionRotation k⁻¹).toContinuousLinearEquiv.differentiableAt]
  have hR : fderiv ℝ (quaternionRotation k⁻¹) q =
      (quaternionRotation k⁻¹).toContinuousLinearEquiv.toContinuousLinearMap :=
    (quaternionRotation k⁻¹).toContinuousLinearEquiv.fderiv
  rw [hR]
  rfl

theorem smoothRho_derivative (k : QuaternionSpinPair) (v : ℍ) (f : SmoothPunctured) :
    smoothRho k (smoothDerivative v f) =
      smoothDerivative (quaternionRotation k v) (smoothRho k f) := by
  apply SmoothPunctured.ext
  intro q hq
  have hq' : quaternionRotation k⁻¹ q ≠ 0 := (map_ne_zero_iff (quaternionRotation k⁻¹) (quaternionRotation k⁻¹).injective).mpr hq
  rw [smoothRho_apply, smoothDerivative_apply _ _ hq', smoothDerivative_apply _ _ hq]
  unfold directional
  rw [smoothRho_fderiv k f hq]
  rw [quaternionRotation_inv, LinearIsometryEquiv.symm_apply_apply]

/-- Direct covariance of the Fueter kernel, including its total value at zero. -/
theorem kernel_rotation (k : QuaternionSpinPair) (q : ℍ) :
    (k.2 : ℍ) * kernel (quaternionRotation k⁻¹ q) = kernel q * (k.1 : ℍ) := by
  rw [kernel_eq, kernel_eq, (quaternionRotation k⁻¹).norm_map]
  simp only [quaternionRotation_apply, Prod.fst_inv, Prod.snd_inv, unitQuaternion_coe_inv,
    star_star, star_mul, mul_smul_comm, smul_mul_assoc]
  congr 1
  calc
    _ = ((k.2 : ℍ) * star (k.2 : ℍ)) * star q * (k.1 : ℍ) := by noncomm_ring
    _ = star q * (k.1 : ℍ) := by
      simp only [← Unitary.coe_star, Unitary.coe_mul_star_self, one_mul]

/-- Ordered real derivatives as smooth punctured functions. -/
def smoothKernelPartial (l : List (Fin 4)) : SmoothPunctured :=
  puncturedSmooth (iteratedPartial l kernel) (kernel_iteratedPartial_regular l).1

@[simp] theorem smoothKernelPartial_apply (l : List (Fin 4)) {q : ℍ} (hq : q ≠ 0) :
    smoothKernelPartial l q = iteratedPartial l kernel q := puncturedSmooth_apply hq

@[simp] theorem smoothKernelPartial_nil : smoothKernelPartial [] = smoothHigherKernel 0 := by
  apply SmoothPunctured.ext
  intro q hq
  rw [smoothKernelPartial_apply _ hq, smoothHigherKernel_apply _ hq]
  rfl

theorem smoothKernelPartial_cons (μ : Fin 4) (l : List (Fin 4)) :
    smoothKernelPartial (μ :: l) = smoothDerivative (coordinateBasis μ) (smoothKernelPartial l) := by
  apply SmoothPunctured.ext
  intro q hq
  rw [smoothKernelPartial_apply _ hq, smoothDerivative_apply _ _ hq]
  exact congrArg (fun A : ℍ →L[ℝ] ℍ => A (coordinateBasis μ)) (puncturedSmooth_fderiv hq).symm

theorem smoothHigherKernel_eq_partial (ν : Fin 3 → ℕ) :
    smoothHigherKernel ν = smoothKernelPartial (spatialDerivativeList ν) := by
  apply SmoothPunctured.ext
  intro q hq
  rw [smoothHigherKernel_apply _ hq, smoothKernelPartial_apply _ hq]
  rfl

theorem smoothRho_kernel (k : QuaternionSpinPair) :
    smoothRho k (smoothKernelPartial []) = MulOpposite.op (k.1 : ℍ) • smoothKernelPartial [] := by
  apply SmoothPunctured.ext
  intro q hq
  rw [smoothRho_apply, smoothPunctured_smul_apply,
    smoothKernelPartial_apply _ ((map_ne_zero_iff (quaternionRotation k⁻¹) (quaternionRotation k⁻¹).injective).mpr hq), smoothKernelPartial_apply _ hq]
  exact kernel_rotation k q

/-- Every rotated ordered real derivative lies in the spatial derivative span. -/
theorem smoothRho_partial_mem (k : QuaternionSpinPair) (l : List (Fin 4)) :
    smoothRho k (smoothKernelPartial l) ∈ kernelDerivativeSpace l.length := by
  induction l with
  | nil =>
    rw [smoothRho_kernel, smoothKernelPartial_nil]
    apply Submodule.smul_mem
    simpa using smoothHigherKernel_mem 0
  | cons μ l ih =>
    rw [smoothKernelPartial_cons, smoothRho_derivative]
    exact smoothDerivative_mem _ ih

/-- Invariance is proved for the actual right-H span, using F1 and the chain rule. -/
theorem smoothRho_mem (r : ℕ) (k : QuaternionSpinPair) {f : SmoothPunctured}
    (hf : f ∈ kernelDerivativeSpace r) : smoothRho k f ∈ kernelDerivativeSpace r := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    change x ∈ Set.range (fun ν : {ν : Fin 3 → ℕ // ∑ j, ν j = r} => smoothHigherKernel ν) at hx
    obtain ⟨⟨ν, hν⟩, rfl⟩ := hx
    change smoothRho k (smoothHigherKernel ν) ∈ kernelDerivativeSpace r
    rw [smoothHigherKernel_eq_partial]
    simpa only [spatialDerivativeList_length, hν] using smoothRho_partial_mem k (spatialDerivativeList ν)
  | zero => simp
  | add x y _ _ hx hy => simpa using (kernelDerivativeSpace r).add_mem hx hy
  | smul c x _ hx => simpa using (kernelDerivativeSpace r).smul_mem c hx

/-- EI7's input action, as a right quaternion linear equivalence on U. -/
def kernelRho (r : ℕ) (k : QuaternionSpinPair) :
    kernelDerivativeSpace r ≃ₗ[ℍᵐᵒᵖ] kernelDerivativeSpace r where
  toFun f := ⟨smoothRho k f, smoothRho_mem r k f.property⟩
  invFun f := ⟨smoothRho k⁻¹ f, smoothRho_mem r k⁻¹ f.property⟩
  left_inv f := Subtype.ext (smoothRho_inv_cancel k f)
  right_inv f := Subtype.ext (smoothRho_cancel_inv k f)
  map_add' f g := Subtype.ext (map_add (smoothRho k) (f : SmoothPunctured) (g : SmoothPunctured))
  map_smul' c f := Subtype.ext (map_smul (smoothRho k) c (f : SmoothPunctured))

@[simp] theorem kernelRho_one (r : ℕ) : kernelRho r 1 = 1 := by
  apply LinearEquiv.ext
  intro f
  exact Subtype.ext (congrArg (fun A => A (f : SmoothPunctured)) smoothRho_one)

theorem kernelRho_mul (r : ℕ) (k l : QuaternionSpinPair) :
    kernelRho r (k * l) = kernelRho r k * kernelRho r l := by
  apply LinearEquiv.ext
  intro f
  exact Subtype.ext (smoothRho_mul k l f)

@[simp] theorem kernelRho_inv (r : ℕ) (k : QuaternionSpinPair) :
    kernelRho r k⁻¹ = (kernelRho r k).symm := by
  apply LinearEquiv.ext
  intro f
  rfl

/-- The central pair acts by minus the identity on the input space. -/
theorem kernelRho_central (r : ℕ) (f : kernelDerivativeSpace r) :
    kernelRho r (-1, -1) f = -f := by
  apply Subtype.ext
  apply SmoothPunctured.ext
  intro q _
  change smoothRho (-1, -1) (f : SmoothPunctured) q = -(f : SmoothPunctured) q
  simp [quaternionRotation, Unitary.coe_neg]

theorem smoothKernelPartial_mem (l : List (Fin 4)) :
    smoothKernelPartial l ∈ kernelDerivativeSpace l.length := by
  simpa using smoothRho_partial_mem 1 l

/-- The spatial definition of U equals the span of all ordered real partials. -/
theorem kernelDerivativeSpace_eq_real_span (r : ℕ) : kernelDerivativeSpace r =
    Submodule.span ℍᵐᵒᵖ (Set.range (fun l : {l : List (Fin 4) // l.length = r} =>
      smoothKernelPartial l)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨ν, hν⟩, rfl⟩
    change smoothHigherKernel ν ∈ Submodule.span ℍᵐᵒᵖ
      (Set.range (fun l : {l : List (Fin 4) // l.length = r} => smoothKernelPartial l))
    rw [smoothHigherKernel_eq_partial]
    exact Submodule.subset_span ⟨⟨spatialDerivativeList ν, (spatialDerivativeList_length ν).trans hν⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨l, hl⟩, rfl⟩
    change smoothKernelPartial l ∈ kernelDerivativeSpace r
    rw [← hl]
    exact smoothKernelPartial_mem l

end MathResearch.Fueter
