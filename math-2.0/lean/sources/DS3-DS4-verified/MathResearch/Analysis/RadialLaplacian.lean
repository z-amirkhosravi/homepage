module
public import MathResearch.Spinor.WeakHarmonic
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-! Four-dimensional radial calculus for the Weyl regularity proof. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion ContDiff BigOperators
open MeasureTheory InnerProductSpace Filter
namespace MathResearch.Spinor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Euclidean Laplacian as iterated directional derivatives in our fixed basis. -/
theorem laplacian_eq_sum_directional {f : ℍ → E} (hf : ContDiff ℝ ∞ f) (q : ℍ) :
    Laplacian.laplacian f q = ∑ i : Fin 4,
      fderiv ℝ (fun x => fderiv ℝ f x (Fueter.coordinateBasis i)) q
        (Fueter.coordinateBasis i) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f quaternionONB]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedFDeriv_two_apply]
  rw [fderiv_clm_apply ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) q)
    (differentiableAt_const _)]
  simp

/-- First derivative of a smooth function of squared radius. -/
theorem fderiv_radial_sq (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h) (q v : ℍ) :
    fderiv ℝ (fun x : ℍ => h (‖x‖ ^ 2)) q v =
      2 * deriv h (‖q‖ ^ 2) * inner ℝ q v := by
  have hd := (hh.differentiable (by simp) (‖q‖ ^ 2)).hasDerivAt.comp_hasFDerivAt q
    (hasStrictFDerivAt_norm_sq q).hasFDerivAt
  change HasFDerivAt (fun x : ℍ => h (‖x‖ ^ 2)) _ q at hd
  rw [hd.fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  ring

/-- In real dimension four, Δ(h(|q|²)) = 8h'(|q|²)+4|q|²h''(|q|²). -/
theorem laplacian_radial_sq (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h) (q : ℍ) :
    Laplacian.laplacian (fun x : ℍ => h (‖x‖ ^ 2)) q =
      8 * deriv h (‖q‖ ^ 2) + 4 * ‖q‖ ^ 2 * deriv (deriv h) (‖q‖ ^ 2) := by
  have hc : ContDiff ℝ ∞ (fun x : ℍ => h (‖x‖ ^ 2)) := hh.comp (contDiff_norm_sq ℝ)
  rw [laplacian_eq_sum_directional hc]
  have hh' : ContDiff ℝ ∞ (deriv h) := hh.deriv'
  have H (v : ℍ) : fderiv ℝ (fun x : ℍ => fderiv ℝ (fun y : ℍ => h (‖y‖ ^ 2)) x v) q v =
      4 * deriv (deriv h) (‖q‖ ^ 2) * (inner ℝ q v) ^ 2 +
        2 * deriv h (‖q‖ ^ 2) * inner ℝ v v := by
    simp_rw [fderiv_radial_sq h hh]
    have hd := ((hh'.differentiable (by simp) (‖q‖ ^ 2)).hasDerivAt.comp_hasFDerivAt q
      (hasStrictFDerivAt_norm_sq q).hasFDerivAt).const_mul 2
    have hi : HasFDerivAt (fun x : ℍ => inner ℝ x v) (innerSL ℝ v) q := by
      simpa only [coe_innerSL_apply, real_inner_comm] using (innerSL ℝ v).hasFDerivAt (x := q)
    have hp := hd.mul hi
    change HasFDerivAt (fun x : ℍ => 2 * deriv h (‖x‖ ^ 2) * inner ℝ x v) _ q at hp
    rw [hp.fderiv]
    simp only [add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul, Function.comp_apply]
    ring
  simp_rw [H]
  simp [Fin.sum_univ_four, Fueter.coordinateBasis_eq, Quaternion.inner_def,
    Quaternion.normSq_def', ← Quaternion.normSq_eq_norm_mul_self, pow_two]
  ring

/-- Translation does not alter the Laplacian. -/
theorem laplacian_translate (f : ℍ → E) (a q : ℍ) :
    Laplacian.laplacian (fun x => f (a + x)) q = Laplacian.laplacian f (a + q) := by
  simp only [laplacian_eq_iteratedFDeriv_orthonormalBasis _ quaternionONB,
    iteratedFDeriv_comp_add_left]

/-- Real dilations multiply the Laplacian by the square of the dilation. -/
theorem laplacian_dilate {f : ℍ → E} (hf : ContDiff ℝ ∞ f) (a : ℝ) (q : ℍ) :
    Laplacian.laplacian (fun x => f (a • x)) q = a ^ 2 • Laplacian.laplacian f (a • q) := by
  let L : ℍ →L[ℝ] ℍ := a • ContinuousLinearMap.id ℝ ℍ
  change Laplacian.laplacian (f ∘ L) q = _
  simp only [laplacian_eq_iteratedFDeriv_orthonormalBasis _ quaternionONB]
  rw [L.iteratedFDeriv_comp_right hf q (by simp : (2 : ℕ) ≤ (∞ : ℕ∞ω))]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, L,
    smul_apply, ContinuousLinearMap.id_apply]
  simp_rw [ContinuousMultilinearMap.map_smul_univ]
  simp [Finset.smul_sum]

/-- Reflection and translation together preserve the Laplacian. -/
theorem laplacian_reflect_translate {f : ℍ → E} (hf : ContDiff ℝ ∞ f) (a q : ℍ) :
    Laplacian.laplacian (fun x => f (a - x)) q = Laplacian.laplacian f (a - q) := by
  have h : ContDiff ℝ ∞ (fun x => f (a + x)) := hf.comp (contDiff_const.add contDiff_id)
  have H := laplacian_dilate h (-1) q
  simpa only [neg_one_smul, sub_eq_add_neg, neg_one_sq, one_smul, laplacian_translate] using H

end MathResearch.Spinor
