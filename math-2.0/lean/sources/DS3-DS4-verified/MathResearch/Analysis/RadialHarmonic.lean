module
public import MathResearch.Analysis.RadialHessian
public import MathResearch.Analysis.RadialMeanODE

/-! A regular radial harmonic function on the four-dimensional ball is constant.
The proof computes its radial and three tangential Hessian entries, then uses
the separate elementary radial ODE lemma. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped Quaternion ContDiff Topology
open InnerProductSpace Set Filter
namespace MathResearch.Spinor
local instance radialHarmonicLocalInstance0 : NormedAddCommGroup ℍ := inferInstance
local instance radialHarmonicLocalInstance1 : NormedSpace ℝ ℍ := inferInstance
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance radialHarmonicLocalInstance2 : NormedAddCommGroup (ℍ →L[ℝ] E) := inferInstance
local instance radialHarmonicLocalInstance3 : NormedSpace ℝ (ℍ →L[ℝ] E) := inferInstance

def radialAxis (A : ℍ → E) (r : ℝ) : E := A (r • (1:ℍ))
def radialAxisFirst (A : ℍ → E) (r : ℝ) : E := fderiv ℝ A (r • (1:ℍ)) 1
def radialAxisSecond (A : ℍ → E) (r : ℝ) : E :=
  fderiv ℝ (fderiv ℝ A) (r • (1:ℍ)) 1 1

theorem norm_axisPoint {r : ℝ} (hr : 0 ≤ r) : ‖r • (1:ℍ)‖ = r := by
  simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]

theorem axisPoint_mem_ball {r : ℝ} (hr : r ∈ Ico (0:ℝ) 1) : r • (1:ℍ) ∈ Ball := by
  rw [mem_ball_iff, norm_axisPoint hr.1]
  exact hr.2

theorem hasDerivAt_radialAxis {A : ℍ → E} {r : ℝ}
    (hA : DifferentiableAt ℝ A (r • (1:ℍ))) :
    HasDerivAt (radialAxis A) (radialAxisFirst A r) r := by
  simpa [radialAxis, radialAxisFirst] using!
    hA.hasFDerivAt.comp_hasDerivAt r ((hasDerivAt_id r).smul_const (1:ℍ))

theorem hasDerivAt_radialAxisFirst {A : ℍ → E} {r : ℝ}
    (hDA : DifferentiableAt ℝ (fderiv ℝ A) (r • (1:ℍ))) :
    HasDerivAt (radialAxisFirst A) (radialAxisSecond A r) r := by
  have h := hDA.hasFDerivAt.clm_apply (hasFDerivAt_const (1:ℍ) (r • (1:ℍ)))
  simpa [radialAxisFirst, radialAxisSecond] using!
    h.comp_hasDerivAt r ((hasDerivAt_id r).smul_const (1:ℍ))

/-- The Laplacian of a radial function is M''(r)+3M'(r)/r away from the center. -/
theorem laplacian_radial_axis {A : ℍ → E}
    (hA : ∀ q ∈ Ball, DifferentiableAt ℝ A q)
    (hDA : ∀ q ∈ Ball, DifferentiableAt ℝ (fderiv ℝ A) q)
    (hrad : ∀ q ∈ Ball, A q = A (‖q‖ • (1:ℍ)))
    {r : ℝ} (hr : r ∈ Ioo (0:ℝ) 1) :
    Laplacian.laplacian A (r • (1:ℍ)) =
      radialAxisSecond A r + (3/r) • radialAxisFirst A r := by
  have hq := axisPoint_mem_ball ⟨hr.1.le,hr.2⟩
  have hq0 : r • (1:ℍ) ≠ 0 := by
    exact smul_ne_zero hr.1.ne' one_ne_zero
  have hM (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :=
    hasDerivAt_radialAxis (hA _ (axisPoint_mem_ball ⟨ht.1.le,ht.2⟩))
  have hM' (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :=
    hasDerivAt_radialAxisFirst (hDA _ (axisPoint_mem_ball ⟨ht.1.le,ht.2⟩))
  have hi (i : Fin 4) (hi : i ≠ 0) : inner ℝ (r • (1:ℍ)) (quaternionONB i) = 0 := by
    fin_cases i <;> simp_all [quaternionONB_apply, Fueter.coordinateBasis_eq, Quaternion.inner_def]
  have H (i : Fin 4) (hi0 : i ≠ 0) :
      fderiv ℝ (fderiv ℝ A) (r • (1:ℍ)) (quaternionONB i) (quaternionONB i) =
        r⁻¹ • radialAxisFirst A r := by
    simpa only [quaternionONB.orthonormal.norm_eq_one, one_pow, norm_axisPoint hr.1.le,
      one_div] using radial_hessian_tangent hrad hM hM' hq hq0 (hDA _ hq) (quaternionONB i) (hi i hi0)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ quaternionONB]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Fin.sum_univ_four]
  rw [H 1 (by decide), H 2 (by decide), H 3 (by decide)]
  have hb : quaternionONB 0 = (1:ℍ) := by simp [Fueter.coordinateBasis_eq]
  rw [hb]
  change radialAxisSecond A r + _ + _ + _ = _
  module

/-- Radial harmonicity and regularity at the center force constancy. -/
theorem radial_harmonic_constant {A : ℍ → E}
    (hA : ∀ q ∈ Ball, DifferentiableAt ℝ A q)
    (hDA : ∀ q ∈ Ball, DifferentiableAt ℝ (fderiv ℝ A) q)
    (hrad : ∀ q ∈ Ball, A q = A (‖q‖ • (1:ℍ)))
    (hzero : fderiv ℝ A 0 1 = 0)
    (hΔ : ∀ q ∈ Ball, Laplacian.laplacian A q = 0)
    {q : ℍ} (hq : q ∈ Ball) : A q = A 0 := by
  have hODE (r : ℝ) (hr : r ∈ Ioo (0:ℝ) 1) :
      r • radialAxisSecond A r + (3:ℝ) • radialAxisFirst A r = 0 := by
    have he := congrArg (fun v : E => r • v) ((laplacian_radial_axis hA hDA hrad hr).symm.trans
      (hΔ _ (axisPoint_mem_ball ⟨hr.1.le,hr.2⟩)))
    simpa only [smul_add, smul_smul, smul_zero, mul_div_cancel₀ _ hr.1.ne'] using he
  have H := MathResearch.Analysis.radialMeanODE_constant
    (M := radialAxis A) (M' := radialAxisFirst A) (M'' := radialAxisSecond A)
    (fun t ht => hasDerivAt_radialAxis (hA _ (axisPoint_mem_ball ht)))
    (fun t ht => hasDerivAt_radialAxisFirst (hDA _ (axisPoint_mem_ball ht)))
    (by simpa [radialAxisFirst] using hzero) hODE
    (r := ‖q‖) ⟨norm_nonneg q, (mem_ball_iff q).mp hq⟩
  rw [hrad q hq]
  simpa only [radialAxis, zero_smul] using H

end MathResearch.Spinor
