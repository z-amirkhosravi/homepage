module
public import MathResearch.Analysis.QuaternionicSphericalAverage
public import MathResearch.Analysis.RadialHarmonic

/-! The four-dimensional spherical mean-value theorem, proved separately from
DS3 and DS4. The compact average is radial and harmonic; its regular radial ODE
then makes it constant. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped Quaternion ContDiff Topology
open MeasureTheory InnerProductSpace Set Filter
namespace MathResearch.Spinor
local instance meanValueLocalInstance0 : NormedAddCommGroup ℍ := inferInstance
local instance meanValueLocalInstance1 : NormedSpace ℝ ℍ := inferInstance
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
local instance meanValueLocalInstance2 : NormedAddCommGroup (ℍ →L[ℝ] E) := inferInstance
local instance meanValueLocalInstance3 : NormedSpace ℝ (ℍ →L[ℝ] E) := inferInstance

/-- Spherical means of a smooth harmonic Banach-valued function equal its central value. -/
theorem sphericalAverage_harmonic {f : ℍ → E} (hf : ContDiffOn ℝ ∞ f Ball)
    (hH : HarmonicOnNhd f Ball) {q : ℍ} (hq : q ∈ Ball) : sphericalAverage f q = f 0 := by
  have hΔ (x : ℍ) (hx : x ∈ Ball) : Laplacian.laplacian (sphericalAverage f) x = 0 := by
    rw [laplacian_sphericalAverage hf hx]
    have he : (fun a : Fueter.UnitQuaternion => Laplacian.laplacian f ((a:ℍ)*x)) = 0 := by
      funext a
      exact (hH _ (unit_mul_mem_ball a hx)).2.self_of_nhds
    rw [he]
    change (∫ _ : Fueter.UnitQuaternion, (0:E) ∂unitQuaternionHaar) = 0
    exact integral_zero _ _
  have h := radial_harmonic_constant
    (fun x hx => (hasFDerivAt_sphericalAverage hf hx).differentiableAt)
    (fun x hx => (hasFDerivAt_fderiv_sphericalAverage hf hx).differentiableAt)
    (fun x _ => sphericalAverage_radial f x)
    (fderiv_sphericalAverage_zero hf 1) hΔ hq
  simpa only [sphericalAverage_zero] using h

/-- The exact spherical mean-value dependency of DS3, now proved independently. -/
theorem sphericalMeanValueOnBall_proved : SphericalMeanValueOnBall := by
  intro E _ _ _ f hf hH q hq
  have he := integral_inv_eq_self (fun a : Fueter.UnitQuaternion => f ((a:ℍ)*q)) unitQuaternionHaar
  simp only [Unitary.coe_inv] at he
  exact he.trans (sphericalAverage_harmonic hf hH hq)

end MathResearch.Spinor
