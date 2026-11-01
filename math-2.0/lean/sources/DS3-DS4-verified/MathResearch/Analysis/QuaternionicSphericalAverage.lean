module
public import MathResearch.Analysis.HarmonicMeanValue
public import MathResearch.Analysis.CompactParametricIntegral
public import MathResearch.Analysis.CompactHaarSymmetry
public import Mathlib.MeasureTheory.Group.Integral

/-! Smooth spherical averaging on the quaternionic ball. Compact integration
and its derivatives are background analysis, separate from DS3. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Quaternion ContDiff Topology
open MeasureTheory Set Filter
namespace MathResearch.Spinor

local instance sphericalLocalInstance0 : NormedAddCommGroup ℍ := inferInstance
local instance sphericalLocalInstance1 : NormedSpace ℝ ℍ := inferInstance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance sphericalLocalInstance2 : NormedAddCommGroup (ℍ →L[ℝ] E) := inferInstance
local instance sphericalLocalInstance3 : NormedSpace ℝ (ℍ →L[ℝ] E) := inferInstance

/-- Average over left unit-quaternion rotations. -/
def sphericalAverage (f : ℍ → E) (q : ℍ) : E :=
  ∫ a : Fueter.UnitQuaternion, f ((a : ℍ)*q) ∂unitQuaternionHaar

/-- Derivative of the rotated function, as an actual continuous linear map. -/
def rotatedDerivative (f : ℍ → E) (q : ℍ) (a : Fueter.UnitQuaternion) : ℍ →L[ℝ] E :=
  (fderiv ℝ f ((a : ℍ)*q)).comp (ContinuousLinearMap.mul ℝ ℍ (a : ℍ))

theorem unit_mul_mem_ball (a : Fueter.UnitQuaternion) {q : ℍ} (hq : q ∈ Ball) :
    (a : ℍ)*q ∈ Ball := by
  rw [mem_ball_iff, norm_mul, Fueter.unitQuaternion_norm, one_mul]
  exact (mem_ball_iff q).mp hq

omit [NormedSpace ℝ E] in
theorem continuousOn_rotatedFunction {f : ℍ → E} (hf : ContinuousOn f Ball) :
    ContinuousOn (fun x : ℍ × Fueter.UnitQuaternion => f ((x.2 : ℍ)*x.1)) (Ball ×ˢ univ) :=
  hf.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst).continuousOn
    (fun x hx => unit_mul_mem_ball x.2 hx.1)

theorem continuousOn_rotatedDerivative {f : ℍ → E} (hf : ContDiffOn ℝ ∞ f Ball) :
    ContinuousOn (Function.uncurry (rotatedDerivative f)) (Ball ×ˢ univ) := by
  have hD := continuousOn_rotatedFunction
    (hf.fderiv_of_isOpen ball_isOpen (m := ∞) (by simp)).continuousOn
  have hL : Continuous (fun x : ℍ × Fueter.UnitQuaternion =>
      ContinuousLinearMap.mul ℝ ℍ (x.2 : ℍ)) :=
    (ContinuousLinearMap.mul ℝ ℍ).continuous.comp (continuous_subtype_val.comp continuous_snd)
  exact hD.clm_comp hL.continuousOn

theorem rotatedDerivative_integrable {f : ℍ → E} (hf : ContDiffOn ℝ ∞ f Ball)
    {q : ℍ} (hq : q ∈ Ball) : Integrable (rotatedDerivative f q) unitQuaternionHaar := by
  have hc : Continuous (rotatedDerivative f q) := by
    apply continuousOn_univ.mp
    exact (continuousOn_rotatedDerivative hf).comp
      (continuous_const.prodMk continuous_id).continuousOn (fun _ _ => ⟨hq, trivial⟩)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem hasFDerivAt_sphericalAverage {f : ℍ → E} (hf : ContDiffOn ℝ ∞ f Ball)
    {q : ℍ} (hq : q ∈ Ball) :
    HasFDerivAt (sphericalAverage f) (∫ a, rotatedDerivative f q a ∂unitQuaternionHaar) q := by
  apply MathResearch.Analysis.hasFDerivAt_integral_compact ball_isOpen
    (continuousOn_rotatedFunction hf.continuousOn) (continuousOn_rotatedDerivative hf)
  · intro x hx a
    exact ((hf.contDiffAt (ball_isOpen.mem_nhds (unit_mul_mem_ball a hx))).differentiableAt
      (by simp)).hasFDerivAt.comp x (ContinuousLinearMap.mul ℝ ℍ (a : ℍ)).hasFDerivAt
  · exact hq

theorem fderiv_sphericalAverage {f : ℍ → E} (hf : ContDiffOn ℝ ∞ f Ball)
    {q : ℍ} (hq : q ∈ Ball) (v : ℍ) :
    fderiv ℝ (sphericalAverage f) q v =
      ∫ a : Fueter.UnitQuaternion, fderiv ℝ f ((a:ℍ)*q) ((a:ℍ)*v) ∂unitQuaternionHaar := by
  rw [(hasFDerivAt_sphericalAverage hf hq).fderiv,
    ContinuousLinearMap.integral_apply (rotatedDerivative_integrable hf hq)]
  rfl

/-- Second derivative of a rotated function. -/
def rotatedSecondDerivative (f : ℍ → E) (q : ℍ) (a : Fueter.UnitQuaternion) :
    ℍ →L[ℝ] ℍ →L[ℝ] E :=
  ((ContinuousLinearMap.compL ℝ ℍ ℍ E).flip (ContinuousLinearMap.mul ℝ ℍ (a : ℍ))).comp
    ((fderiv ℝ (fderiv ℝ f) ((a : ℍ)*q)).comp (ContinuousLinearMap.mul ℝ ℍ (a : ℍ)))

theorem continuousOn_rotatedSecondDerivative {f : ℍ → E} (hf : ContDiffOn ℝ ∞ f Ball) :
    ContinuousOn (Function.uncurry (rotatedSecondDerivative f)) (Ball ×ˢ univ) := by
  have hD := continuousOn_rotatedDerivative
    (hf.fderiv_of_isOpen ball_isOpen (m := ∞) (by simp))
  have hL : Continuous (fun x : ℍ × Fueter.UnitQuaternion =>
      (ContinuousLinearMap.compL ℝ ℍ ℍ E).flip (ContinuousLinearMap.mul ℝ ℍ (x.2 : ℍ))) :=
    (ContinuousLinearMap.compL ℝ ℍ ℍ E).flip.continuous.comp
      ((ContinuousLinearMap.mul ℝ ℍ).continuous.comp (continuous_subtype_val.comp continuous_snd))
  exact hL.continuousOn.clm_comp hD

theorem hasFDerivAt_averageDerivative {f : ℍ → E} (hf : ContDiffOn ℝ ∞ f Ball)
    {q : ℍ} (hq : q ∈ Ball) :
    HasFDerivAt (fun x => ∫ a, rotatedDerivative f x a ∂unitQuaternionHaar)
      (∫ a, rotatedSecondDerivative f q a ∂unitQuaternionHaar) q := by
  apply MathResearch.Analysis.hasFDerivAt_integral_compact ball_isOpen
    (continuousOn_rotatedDerivative hf) (continuousOn_rotatedSecondDerivative hf)
  · intro x hx a
    have hdf := hf.fderiv_of_isOpen ball_isOpen (m := ∞) (by simp)
    have h := ((hdf.contDiffAt (ball_isOpen.mem_nhds (unit_mul_mem_ball a hx))).differentiableAt
      (by simp)).hasFDerivAt.comp x (ContinuousLinearMap.mul ℝ ℍ (a : ℍ)).hasFDerivAt
    exact ((ContinuousLinearMap.compL ℝ ℍ ℍ E).flip
      (ContinuousLinearMap.mul ℝ ℍ (a : ℍ))).hasFDerivAt.comp x h
  · exact hq

theorem hasFDerivAt_fderiv_sphericalAverage {f : ℍ → E} (hf : ContDiffOn ℝ ∞ f Ball)
    {q : ℍ} (hq : q ∈ Ball) :
    HasFDerivAt (fderiv ℝ (sphericalAverage f))
      (∫ a, rotatedSecondDerivative f q a ∂unitQuaternionHaar) q := by
  apply (hasFDerivAt_averageDerivative hf hq).congr_of_eventuallyEq
  filter_upwards [ball_isOpen.mem_nhds hq] with x hx
  exact (hasFDerivAt_sphericalAverage hf hx).fderiv

theorem rotatedSecondDerivative_integrable {f : ℍ → E} (hf : ContDiffOn ℝ ∞ f Ball)
    {q : ℍ} (hq : q ∈ Ball) : Integrable (rotatedSecondDerivative f q) unitQuaternionHaar := by
  exact MathResearch.Analysis.integrable_compact_slice
    (continuousOn_rotatedSecondDerivative hf) hq

/-- The Hessian of the average is the average of the rotated Hessians. -/
theorem secondFDeriv_sphericalAverage {f : ℍ → E} (hf : ContDiffOn ℝ ∞ f Ball)
    {q : ℍ} (hq : q ∈ Ball) (v w : ℍ) :
    fderiv ℝ (fderiv ℝ (sphericalAverage f)) q v w =
      ∫ a : Fueter.UnitQuaternion,
        fderiv ℝ (fderiv ℝ f) ((a:ℍ)*q) ((a:ℍ)*v) ((a:ℍ)*w) ∂unitQuaternionHaar := by
  rw [(hasFDerivAt_fderiv_sphericalAverage hf hq).fderiv,
    ContinuousLinearMap.integral_apply (rotatedSecondDerivative_integrable hf hq),
    ContinuousLinearMap.integral_apply ((rotatedSecondDerivative_integrable hf hq).apply_continuousLinearMap v)]
  rfl

/-- Spherical averaging commutes with the Euclidean Laplacian. -/
theorem laplacian_sphericalAverage {f : ℍ → E} (hf : ContDiffOn ℝ ∞ f Ball)
    {q : ℍ} (hq : q ∈ Ball) :
    Laplacian.laplacian (sphericalAverage f) q =
      ∫ a : Fueter.UnitQuaternion, Laplacian.laplacian f ((a:ℍ)*q) ∂unitQuaternionHaar := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ quaternionONB]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, secondFDeriv_sphericalAverage hf hq]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro a
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
      (quaternionONB.map (Fueter.quaternionRotation (a,1)))]
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, OrthonormalBasis.map_apply]
    simp [Fueter.quaternionRotation]
  · intro i _
    exact ((rotatedSecondDerivative_integrable hf hq).apply_continuousLinearMap
      (quaternionONB i)).apply_continuousLinearMap (quaternionONB i)

@[simp] theorem sphericalAverage_zero [CompleteSpace E] (f : ℍ → E) : sphericalAverage f 0 = f 0 := by
  simp [sphericalAverage]

theorem sphericalAverage_unit_mul (f : ℍ → E) (b : Fueter.UnitQuaternion) (q : ℍ) :
    sphericalAverage f ((b : ℍ)*q) = sphericalAverage f q := by
  simpa only [sphericalAverage, Submonoid.coe_mul, mul_assoc] using
    (integral_mul_right_eq_self (μ := unitQuaternionHaar)
      (fun a : Fueter.UnitQuaternion => f ((a : ℍ)*q)) b)

/-- The average depends only on the Euclidean radius. -/
theorem sphericalAverage_radial (f : ℍ → E) (q : ℍ) :
    sphericalAverage f q = sphericalAverage f (‖q‖ • (1 : ℍ)) := by
  by_cases hq : q = 0
  · simp [hq]
  · have he : (Fueter.normalizeQuaternion q hq : ℍ) * (‖q‖ • (1 : ℍ)) = q := by
      change (‖q‖⁻¹ • q) * (‖q‖ • (1 : ℍ)) = q
      simp [smul_smul, norm_ne_zero_iff.mpr hq]
    calc
      _ = sphericalAverage f ((Fueter.normalizeQuaternion q hq : ℍ) * (‖q‖ • (1 : ℍ))) :=
        congrArg (sphericalAverage f) he.symm
      _ = _ := sphericalAverage_unit_mul f _ _

/-- The first derivative at the center vanishes by compact symmetry. -/
theorem fderiv_sphericalAverage_zero {f : ℍ → E} (hf : ContDiffOn ℝ ∞ f Ball) (v : ℍ) :
    fderiv ℝ (sphericalAverage f) 0 v = 0 := by
  rw [fderiv_sphericalAverage hf (by simp [mem_ball_iff])]
  apply integral_eq_zero_of_mul_left_eq_neg (g := (-1 : Fueter.UnitQuaternion))
  intro a
  simp [Unitary.coe_neg]

end MathResearch.Spinor
