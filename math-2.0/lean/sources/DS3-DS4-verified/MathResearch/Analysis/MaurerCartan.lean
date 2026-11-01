module
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Tactic

/-! Maurer–Cartan for the logarithmic derivative of a matrix-valued map over a
finite-dimensional real normed associative algebra. The inverse is supplied as a
function, with its differentiability and the two inverse identities explicit.
This background theorem is independent of the quaternionic ball calculation. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Topology Matrix.Norms.Elementwise
namespace MathResearch.Analysis

variable {E A ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]
  [Fintype ι] [DecidableEq ι]

local notation "M" => Matrix ι ι A

/-- Multiplication as a continuous bilinear map, without choosing an algebra norm. -/
def algebraMulCLM : M →L[ℝ] M →L[ℝ] M :=
  (LinearMap.toContinuousLinearMap.toLinearMap.comp (LinearMap.mul ℝ M)).toContinuousLinearMap

@[simp] theorem algebraMulCLM_apply (a b : M) : algebraMulCLM a b = a * b := rfl

theorem fderiv_algebra_mul {f g : E → M} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (v : E) :
    fderiv ℝ (fun y => f y * g y) x v =
      f x * fderiv ℝ g x v + fderiv ℝ f x v * g x := by
  exact congrArg (fun L : E →L[ℝ] M => L v) (algebraMulCLM.fderiv_of_bilinear hf hg)

/-- The Maurer–Cartan equation dθ(v,w)+[θ(v),θ(w)]=0 for θ=g df.
The hypotheses say that f is C², g is differentiable, gf=1 near x and fg=1 at x. -/
theorem maurerCartan {f g : E → M} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : DifferentiableAt ℝ g x)
    (hgf : (fun y => g y * f y) =ᶠ[𝓝 x] (fun _ => 1))
    (hfg : f x * g x = 1) (v w : E) :
    fderiv ℝ (fun y => g y * fderiv ℝ f y w) x v -
      fderiv ℝ (fun y => g y * fderiv ℝ f y v) x w +
      (g x * fderiv ℝ f x v * (g x * fderiv ℝ f x w) -
       g x * fderiv ℝ f x w * (g x * fderiv ℝ f x v)) = 0 := by
  have hf1 : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hf2 : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hi (u : E) : fderiv ℝ g x u = -(g x * fderiv ℝ f x u * g x) := by
    have hz : g x * fderiv ℝ f x u + fderiv ℝ g x u * f x = 0 := by
      rw [← fderiv_algebra_mul hg hf1 u, hgf.fderiv_eq]
      simp
    have h := congrArg (fun a : M => a * g x) hz
    simp only [add_mul, mul_assoc, hfg, mul_one, zero_mul] at h
    simpa only [mul_assoc] using eq_neg_of_add_eq_zero_right h
  rw [fderiv_algebra_mul hg (hf2.clm_apply (differentiableAt_const w)),
    fderiv_algebra_mul hg (hf2.clm_apply (differentiableAt_const v)),
    fderiv_clm_apply hf2 (differentiableAt_const w),
    fderiv_clm_apply hf2 (differentiableAt_const v)]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    fderiv_fun_const, Pi.zero_apply, zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply]
  rw [hi v, hi w, (hf.isSymmSndFDerivAt (by norm_num)).eq v w]
  noncomm_ring

end MathResearch.Analysis
