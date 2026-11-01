module
public import MathResearch.Spinor.Sp11
public import MathResearch.Spinor.RepresentationCalculus

/-! Differentiating the actual equivariant lift in the moving section. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion BigOperators Matrix.Norms.Elementwise
namespace MathResearch.Spinor

/-- Evaluation of a quaternion matrix entry as a real continuous linear map. -/
def entryCLM (i j : Fin 2) : QuaternionMatrix2 →L[ℝ] ℍ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => g i j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

@[simp] theorem entryCLM_apply (i j : Fin 2) (g : QuaternionMatrix2) : entryCLM i j g = g i j := rfl

theorem differentiableAt_groupOrigin {g : QuaternionMatrix2} (hd : g 1 1 ≠ 0) :
    DifferentiableAt ℝ groupOrigin g := by
  exact ((entryCLM 0 1).hasFDerivAt.mul'
    ((hasFDerivAt_inv' hd).comp g (entryCLM 1 1).hasFDerivAt)).differentiableAt

theorem fderiv_groupOrigin {g : QuaternionMatrix2} (hd : g 1 1 ≠ 0) (V : QuaternionMatrix2) :
    fderiv ℝ groupOrigin g V = V 0 1 * (g 1 1)⁻¹ -
      (g 0 1) * ((g 1 1)⁻¹ * V 1 1 * (g 1 1)⁻¹) := by
  have h := (entryCLM 0 1).hasFDerivAt.mul'
    ((hasFDerivAt_inv' hd).comp g (entryCLM 1 1).hasFDerivAt)
  change HasFDerivAt groupOrigin _ g at h
  rw [h.fderiv]
  simp [ContinuousLinearMap.mulLeftRight_apply, sub_eq_add_neg, add_comm]

theorem ballSection_lowerRight_inv (q : ℍ) :
    (ballSection q 1 1)⁻¹ = (Real.sqrt (ballScale q) : ℍ) := by
  have he : ballSection q 1 1 = ((Real.sqrt (ballScale q))⁻¹ : ℝ) := by
    ext <;> simp [ballSection, -Quaternion.coe_inv]
  rw [he, ← Quaternion.coe_inv, inv_inv]

theorem groupOrigin_ballSection (q : ℍ) (hq : q ∈ Ball) : groupOrigin (ballSection q) = q := by
  have hs : Real.sqrt (ballScale q) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  rw [groupOrigin, ballSection_lowerRight_inv]
  rw [show (Real.sqrt (ballScale q) : ℍ) = Real.sqrt (ballScale q) • (1 : ℍ) by ext <;> simp]
  change ((Real.sqrt (ballScale q))⁻¹ • q) * (Real.sqrt (ballScale q) • (1 : ℍ)) = q
  rw [mul_smul_comm, smul_mul_assoc, mul_one, smul_smul, mul_inv_cancel₀ hs, one_smul]

theorem compactRight_ballSection (q : ℍ) (hq : q ∈ Ball) : compactRight (ballSection q) = 1 := by
  rw [compactRight, groupOrigin_ballSection q hq]
  simp [ballSection, smul_smul, (Real.sqrt_pos.mpr hq).ne']

theorem fderiv_groupOrigin_section (q v : ℍ) (hq : q ∈ Ball) :
    fderiv ℝ groupOrigin (ballSection q) (ballSection q * tangentMatrix v) = ballScale q • v := by
  rw [fderiv_groupOrigin (ballSection_isSp11 q hq).lowerRight_ne_zero, ballSection_lowerRight_inv]
  have hs : Real.sqrt (ballScale q) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  ext <;> simp [ballSection, tangentMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [hs]
  all_goals try simp only [ballScale, Quaternion.normSq_def']
  all_goals ring

/-- A real line with the same tangent as σ(q)exp(t ξ_v) at zero. -/
def rightAffinePath (g : QuaternionMatrix2) (v : ℍ) (t : ℝ) : QuaternionMatrix2 :=
  g + t • (g * tangentMatrix v)

@[simp] theorem rightAffinePath_zero (g : QuaternionMatrix2) (v : ℍ) : rightAffinePath g v 0 = g := by
  simp [rightAffinePath]

theorem rightAffinePath_hasDerivAt (g : QuaternionMatrix2) (v : ℍ) :
    HasDerivAt (rightAffinePath g v) (g * tangentMatrix v) 0 := by
  simpa only [rightAffinePath, one_smul] using!
    ((hasDerivAt_id (0 : ℝ)).smul_const (g*tangentMatrix v)).const_add g

theorem groupOrigin_section_hasDerivAt (q v : ℍ) (hq : q ∈ Ball) :
    HasDerivAt (fun t => groupOrigin (rightAffinePath (ballSection q) v t)) (ballScale q • v) 0 := by
  have hd := (differentiableAt_groupOrigin (ballSection_isSp11 q hq).lowerRight_ne_zero).hasFDerivAt
  have hh := (show HasFDerivAt groupOrigin _ (rightAffinePath (ballSection q) v 0) from by simpa using hd).comp_hasDerivAt 0
    (rightAffinePath_hasDerivAt (ballSection q) v)
  simpa only [Function.comp_def, fderiv_groupOrigin_section q v hq] using hh

/-- The second compact coordinate has derivative -C_v, so its inverse contributes +C_v. -/
theorem compactRight_section_hasDerivAt (q v : ℍ) (hq : q ∈ Ball) :
    HasDerivAt (fun t => compactRight (rightAffinePath (ballSection q) v t)) (-connectionCoefficient q v) 0 := by
  have hbase := groupOrigin_section_hasDerivAt q v hq
  have hscale := (show HasFDerivAt ballScale _ (groupOrigin (rightAffinePath (ballSection q) v 0)) from
    by simpa [groupOrigin_ballSection q hq] using hasFDerivAt_ballScale q).comp_hasDerivAt 0 hbase
  have hsqrt := hscale.sqrt (by simpa [groupOrigin_ballSection q hq] using (ne_of_gt hq))
  have hd := (entryCLM 1 1).hasFDerivAt.comp_hasDerivAt 0 (rightAffinePath_hasDerivAt (ballSection q) v)
  have h := hsqrt.smul hd
  change HasDerivAt (fun t => compactRight (rightAffinePath (ballSection q) v t)) _ 0 at h
  convert! h using 1
  have hs : Real.sqrt (ballScale q) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hs2 := Real.sq_sqrt (le_of_lt hq)
  simp only [Function.comp_def, rightAffinePath_zero, groupOrigin_ballSection q hq, entryCLM_apply]
  ext <;> simp [ballSection, tangentMatrix, Matrix.mul_apply, Fin.sum_univ_two,
    connectionCoefficient, Quaternion.inner_def, innerSL_apply_apply] <;> field_simp [hs]
  all_goals try rw [hs2]
  all_goals try simp only [ballScale, Quaternion.normSq_def']
  all_goals ring

/-- Lift from section data, expressed in the actual compact coordinate k_R. -/
def frameLift (n : ℕ) (U : ℍ → BinaryForm n) (g : QuaternionMatrix2) : BinaryForm n :=
  polynomialRepresentation n (quaternionMatrix ((compactRight g)⁻¹)) (U (groupOrigin g))

@[simp] theorem frameLift_section (n : ℕ) (U : ℍ → BinaryForm n) (q : ℍ) (hq : q ∈ Ball) :
    frameLift n U (ballSection q) = U q := by
  simp [frameLift, compactRight_ballSection q hq, groupOrigin_ballSection q hq]

/-- Infinitesimal right differentiation, in an ambient differentiable representative. -/
def rightLieDerivative (n : ℕ) (F : QuaternionMatrix2 → BinaryForm n) (g : QuaternionMatrix2) (v : ℍ) :
    BinaryForm n := deriv (fun t => F (rightAffinePath g v t)) 0

/-- The moving-frame formula L7, obtained by differentiating the actual lift. -/
theorem frameLift_section_hasDerivAt (m : ℕ) (U : ℍ → BinaryForm (m+1)) (q v : ℍ)
    (hq : q ∈ Ball) (hU : DifferentiableAt ℝ U q) :
    HasDerivAt (fun t => frameLift (m+1) U (rightAffinePath (ballSection q) v t))
      (ballScale q • fderiv ℝ U q v + infinitesimalAction m (quaternionMatrix (connectionCoefficient q v)) (U q)) 0 := by
  have hk := compactRight_section_hasDerivAt q v hq
  have hi := (hasFDerivAt_inv' (show compactRight (rightAffinePath (ballSection q) v 0) ≠ 0 by
    simp [compactRight_ballSection q hq])).comp_hasDerivAt 0 hk
  have hi' : HasDerivAt (fun t => (compactRight (rightAffinePath (ballSection q) v t))⁻¹)
      (connectionCoefficient q v) 0 := by
    simpa [compactRight_ballSection q hq, ContinuousLinearMap.mulLeftRight_apply] using! hi
  have hu := (show HasFDerivAt U (fderiv ℝ U q) (groupOrigin (rightAffinePath (ballSection q) v 0)) from
    by simpa [groupOrigin_ballSection q hq] using hU.hasFDerivAt).comp_hasDerivAt 0
      (groupOrigin_section_hasDerivAt q v hq)
  let A := fun z : ℍ × BinaryForm (m+1) => polynomialRepresentation (m+1) (quaternionMatrix z.1) z.2
  have ha : HasFDerivAt A (fderiv ℝ A (1,U q))
      ((compactRight (rightAffinePath (ballSection q) v 0))⁻¹, U (groupOrigin (rightAffinePath (ballSection q) v 0))) := by
    simpa [compactRight_ballSection q hq, groupOrigin_ballSection q hq] using
      ((contDiff_quaternionPolynomialRepresentation (m+1)).differentiable (by simp) (1,U q)).hasFDerivAt
  have h := ha.comp_hasDerivAt 0 (hi'.prodMk hu)
  simpa only [A, frameLift, Function.comp_def, fderiv_quaternionAction_pair, map_smul, add_comm] using h

/-- SC1's changing-frame identity, for every real tangent direction. -/
theorem SC1_frame_v1 (m : ℕ) (U : ℍ → BinaryForm (m+1)) (q v : ℍ)
    (hq : q ∈ Ball) (hU : DifferentiableAt ℝ U q) :
    rightLieDerivative (m+1) (frameLift (m+1) U) (ballSection q) v =
      ballScale q • fderiv ℝ U q v + infinitesimalAction m (quaternionMatrix (connectionCoefficient q v)) (U q) :=
  (frameLift_section_hasDerivAt m U q v hq hU).deriv

theorem groupOrigin_compact_mul (g : QuaternionMatrix2) (a b : ℍ) (hb : b ≠ 0) :
    groupOrigin (g * compactMatrix a b) = groupOrigin g := by
  simp [groupOrigin, compactMatrix, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc, hb]

theorem compactRight_compact_mul (g : QuaternionMatrix2) (a b : ℍ) (hb : b ≠ 0) :
    compactRight (g * compactMatrix a b) = compactRight g * b := by
  rw [compactRight, groupOrigin_compact_mul g a b hb]
  simp [compactRight, compactMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- The lift satisfies right equivariance as an actual function, including its inverse convention. -/
theorem frameLift_equivariant (n : ℕ) (U : ℍ → BinaryForm n) (g : QuaternionMatrix2)
    (a b : ℍ) (hb : b ≠ 0) :
    frameLift n U (g * compactMatrix a b) =
      polynomialRepresentation n (quaternionMatrix b⁻¹) (frameLift n U g) := by
  simp only [frameLift, groupOrigin_compact_mul g a b hb, compactRight_compact_mul g a b hb,
    mul_inv_rev, quaternionMatrix_mul, map_mul]
  rfl

/-- Right K-equivariance of a matrix-valued representative, imposed only on G. -/
def RightEquivariant (n : ℕ) (F : QuaternionMatrix2 → BinaryForm n) : Prop :=
  ∀ g, IsSp11 g → ∀ a b : ℍ, Quaternion.normSq a = 1 → Quaternion.normSq b = 1 →
    F (g * compactMatrix a b) = polynomialRepresentation n (quaternionMatrix b⁻¹) (F g)

/-- Every equivariant function is recovered on G from its section values. -/
theorem frameLift_recover (n : ℕ) (F : QuaternionMatrix2 → BinaryForm n)
    (hF : RightEquivariant n F) {g : QuaternionMatrix2} (hg : IsSp11 g) :
    frameLift n (fun q => F (ballSection q)) g = F g := by
  have he := hF (ballSection (groupOrigin g)) (ballSection_isSp11 _ (groupOrigin_mem_ball hg))
    (compactLeft g) (compactRight g) (compactLeft_unit hg) (compactRight_unit hg)
  rw [← section_compact_decomposition hg] at he
  exact he.symm

/-- The concrete lift is differentiable at every group point when the section data is. -/
theorem differentiableAt_frameLift (n : ℕ) (U : ℍ → BinaryForm n) {g : QuaternionMatrix2}
    (hg : IsSp11 g) (hU : DifferentiableAt ℝ U (groupOrigin g)) :
    DifferentiableAt ℝ (frameLift n U) g := by
  have ho := differentiableAt_groupOrigin hg.lowerRight_ne_zero
  have hs := (hasFDerivAt_ballScale (groupOrigin g)).differentiableAt.comp g ho
  have hsqrt := hs.sqrt (ne_of_gt (groupOrigin_mem_ball hg))
  have hk : DifferentiableAt ℝ compactRight g := hsqrt.smul (entryCLM 1 1).differentiableAt
  have hk0 : compactRight g ≠ 0 := by
    intro h
    have := compactRight_unit hg
    simp [h] at this
  have hi := (hasFDerivAt_inv' hk0).differentiableAt.comp g hk
  have hp : DifferentiableAt ℝ (fun x : QuaternionMatrix2 => ((compactRight x)⁻¹, U (groupOrigin x))) g :=
    hi.prodMk (hU.comp g ho)
  change DifferentiableAt ℝ (fun x : QuaternionMatrix2 => polynomialRepresentation n (quaternionMatrix ((compactRight x)⁻¹)) (U (groupOrigin x))) g
  exact ((contDiff_quaternionPolynomialRepresentation n).differentiable (by simp) ((compactRight g)⁻¹, U (groupOrigin g))).comp g hp

/-- Agreement of the line derivative with the invariant tangent vector gξ_v. -/
theorem rightLieDerivative_eq_fderiv (n : ℕ) (F : QuaternionMatrix2 → BinaryForm n)
    (g : QuaternionMatrix2) (hF : DifferentiableAt ℝ F g) (v : ℍ) :
    rightLieDerivative n F g v = fderiv ℝ F g (g * tangentMatrix v) := by
  exact ((show HasFDerivAt F (fderiv ℝ F g) (rightAffinePath g v 0) from by simpa using hF.hasFDerivAt).comp_hasDerivAt 0
    (rightAffinePath_hasDerivAt g v)).deriv

/-- Thus any differentiable group path with this tangent gives the same derivative. -/
theorem rightLieDerivative_eq_path (n : ℕ) (F : QuaternionMatrix2 → BinaryForm n)
    (g : QuaternionMatrix2) (hF : DifferentiableAt ℝ F g) (v : ℍ)
    (γ : ℝ → QuaternionMatrix2) (hγ0 : γ 0 = g) (hγ : HasDerivAt γ (g*tangentMatrix v) 0) :
    deriv (fun t => F (γ t)) 0 = rightLieDerivative n F g v := by
  rw [rightLieDerivative_eq_fderiv n F g hF v]
  exact ((show HasFDerivAt F (fderiv ℝ F g) (γ 0) from hγ0.symm ▸ hF.hasFDerivAt).comp_hasDerivAt 0 hγ).deriv

end MathResearch.Spinor
