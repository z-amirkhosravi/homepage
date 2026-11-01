module
public import MathResearch.Spinor.MobiusLaws
public import MathResearch.Spinor.PolynomialUnitary
public import Mathlib.MeasureTheory.Function.Jacobian

/-! The actual real derivative, determinant, and multiplier norm of the ball action. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion Matrix.Norms.Elementwise
namespace MathResearch.Spinor

theorem mobiusPoint_mul_denominator (g : QuaternionMatrix2) {q : ℍ}
    (hJ : mobiusDenominator g q ≠ 0) :
    mobiusPoint g q * mobiusDenominator g q = g 0 0*q+g 0 1 := by
  simp [mobiusPoint,hJ]

def mobiusLeftFactor (g : QuaternionMatrix2) (q : ℍ) : ℍ := g 0 0-mobiusPoint g q*g 1 0

def mobiusDerivative (g : QuaternionMatrix2) (q : ℍ) : ℍ →L[ℝ] ℍ :=
  (Fueter.quaternionMulLeft (mobiusLeftFactor g q)).toContinuousLinearMap.comp
    (Fueter.quaternionMulRight ((mobiusDenominator g q)⁻¹)).toContinuousLinearMap

@[simp] theorem mobiusDerivative_apply (g : QuaternionMatrix2) (q v : ℍ) :
    mobiusDerivative g q v = mobiusLeftFactor g q*v*(mobiusDenominator g q)⁻¹ := by
  simp [mobiusDerivative,Fueter.quaternionMulLeft,Fueter.quaternionMulRight,mul_assoc]

theorem hasFDerivAt_mobiusPoint (g : QuaternionMatrix2) {q : ℍ}
    (hJ : mobiusDenominator g q ≠ 0) : HasFDerivAt (mobiusPoint g) (mobiusDerivative g q) q := by
  have hJd : HasFDerivAt (mobiusDenominator g)
      (Fueter.quaternionMulLeft (g 1 0)).toContinuousLinearMap q :=
    (Fueter.quaternionMulLeft (g 1 0)).toContinuousLinearMap.hasFDerivAt.add_const _
  have hNd : HasFDerivAt (fun x : ℍ => g 0 0*x+g 0 1)
      (Fueter.quaternionMulLeft (g 0 0)).toContinuousLinearMap q :=
    (Fueter.quaternionMulLeft (g 0 0)).toContinuousLinearMap.hasFDerivAt.add_const _
  convert! hNd.mul' ((hasFDerivAt_inv' hJ).comp q hJd) using 1
  apply ContinuousLinearMap.ext; intro v
  simp [mobiusDerivative,Fueter.quaternionMulLeft,Fueter.quaternionMulRight,
    ContinuousLinearMap.mulLeftRight_apply,mobiusLeftFactor,mobiusPoint]
  noncomm_ring

theorem section_product_first_entry (g : QuaternionMatrix2) (q : ℍ) (i : Fin 2) :
    (g*ballSection q) i 0=(Real.sqrt (ballScale q))⁻¹ • (g i 0+g i 1*star q) := by
  simp [ballSection,Matrix.mul_apply,Fin.sum_univ_two,smul_add]

theorem horizontal_column_norm {h : QuaternionMatrix2} (hh : IsSp11 h) :
    Quaternion.normSq (h 0 0-groupOrigin h*h 1 0)=ballScale (groupOrigin h) := by
  have he : h 0 0-groupOrigin h*h 1 0=ballScale (groupOrigin h) • h 0 0 := by
    rw [hh.lowerLeft_eq,← mul_assoc,Quaternion.self_mul_star]
    rw [Quaternion.coe_mul_eq_smul]
    simp [ballScale,sub_eq_add_neg,add_smul]
  have hu := compactLeft_unit hh
  rw [compactLeft,Quaternion.normSq_smul,Real.sq_sqrt (groupOrigin_mem_ball hh).le] at hu
  rw [he,Quaternion.normSq_smul]
  calc
    _ = ballScale (groupOrigin h) * (ballScale (groupOrigin h)*Quaternion.normSq (h 0 0)) := by ring
    _ = _ := by rw [hu,mul_one]

theorem horizontal_column_section {g : QuaternionMatrix2} (hg : IsSp11 g) {q : ℍ} (hq : q ∈ Ball) :
    (g*ballSection q) 0 0-groupOrigin (g*ballSection q)*(g*ballSection q) 1 0 =
      Real.sqrt (ballScale q) • mobiusLeftFactor g q := by
  have he := mobiusPoint_mul_denominator g (mobiusDenominator_ne_zero hg hq)
  have hb : g 0 1-mobiusPoint g q*g 1 1 = -(mobiusLeftFactor g q*q) := by
    unfold mobiusDenominator at he
    unfold mobiusLeftFactor
    rw [sub_mul,neg_sub,mul_assoc]
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [mul_add,add_comm] using he.symm
  rw [groupOrigin_section_product g q hq,section_product_first_entry,section_product_first_entry,mul_smul_comm,← smul_sub]
  have hinside : g 0 0+g 0 1*star q-mobiusPoint g q*(g 1 0+g 1 1*star q)=
      ballScale q • mobiusLeftFactor g q := by
    calc
      _ = mobiusLeftFactor g q+(g 0 1-mobiusPoint g q*g 1 1)*star q := by unfold mobiusLeftFactor; noncomm_ring
      _ = _ := by
        rw [hb,neg_mul,mul_assoc,Quaternion.self_mul_star]
        rw [Quaternion.mul_coe_eq_smul]
        simp [ballScale,sub_eq_add_neg,add_smul]
  rw [hinside,smul_smul]
  congr 1
  have hs := Real.sq_sqrt hq.le
  have hn := (Real.sqrt_pos.mpr hq).ne'
  field_simp
  exact hs.symm

theorem mobiusLeftFactor_normSq {g : QuaternionMatrix2} (hg : IsSp11 g) {q : ℍ} (hq : q ∈ Ball) :
    Quaternion.normSq (mobiusLeftFactor g q)=(Quaternion.normSq (mobiusDenominator g q))⁻¹ := by
  have h := horizontal_column_norm (hg.mul (ballSection_isSp11 q hq))
  rw [horizontal_column_section hg hq,Quaternion.normSq_smul,Real.sq_sqrt hq.le,
    groupOrigin_section_product g q hq,ballScale_mobius hg hq,div_eq_mul_inv] at h
  exact mul_left_cancel₀ (ne_of_gt hq) h

/-- The real four-dimensional Jacobian is |cq+d|⁻⁸. -/
theorem mobiusJacobian (g : QuaternionMatrix2) (hg : IsSp11 g) (q : ℍ) (hq : q ∈ Ball) :
    (fderiv ℝ (mobiusPoint g) q).det = (Quaternion.normSq (mobiusDenominator g q))⁻¹ ^ 4 := by
  rw [(hasFDerivAt_mobiusPoint g (mobiusDenominator_ne_zero hg hq)).fderiv]
  change LinearMap.det ((Fueter.quaternionMulLeft (mobiusLeftFactor g q)).comp
    (Fueter.quaternionMulRight ((mobiusDenominator g q)⁻¹))) = _
  rw [LinearMap.det_comp,Fueter.det_quaternionMulLeft,Fueter.det_quaternionMulRight,
    mobiusLeftFactor_normSq hg hq,map_inv₀]
  ring

/-- The exact multiplier norm, independent of the differential equation. -/
theorem ballAction_norm (n : ℕ) (g : QuaternionMatrix2) (f : ℍ → BinaryForm n) (q : ℍ) :
    ‖ballAction n g f q‖ = ‖mobiusDenominator g q‖⁻¹ ^ (n+2)*‖f (mobiusPoint g q)‖ := by
  rw [ballAction,norm_smul,quaternionAction_norm,norm_inv]
  rw [Real.norm_eq_abs,abs_of_nonneg Quaternion.normSq_nonneg,Quaternion.normSq_eq_norm_mul_self]
  simp only [norm_inv,mul_inv_rev,pow_succ]
  ring

end MathResearch.Spinor
