module
public import MathResearch.Spinor.ProjectedConnection
public import MathResearch.Analysis.MaurerCartan
public import MathResearch.Fueter.Kernel
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Matrix.Normed

/-! The actual derivative of the ball section and its nonflat compact connection. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion BigOperators Matrix.Norms.Elementwise Topology
namespace MathResearch.Spinor

local instance : StarModule ℝ ℍ where
  star_smul r q := by simpa only [star_trivial] using Quaternion.star_smul r q

abbrev QuaternionMatrix2 := Matrix (Fin 2) (Fin 2) ℍ

/-- The positive defining function s=1-|q|² of the unit ball. -/
def ballScale (q : ℍ) : ℝ := 1 - Quaternion.normSq q

def Ball : Set ℍ := {q | 0 < ballScale q}

theorem mem_ball_iff (q : ℍ) : q ∈ Ball ↔ ‖q‖ < 1 := by
  simp only [Ball, Set.mem_ofPred_eq, ballScale, Quaternion.normSq_eq_norm_mul_self]
  constructor <;> intro h
  · nlinarith [norm_nonneg q]
  · nlinarith [norm_nonneg q]

theorem hasFDerivAt_ballScale (q : ℍ) :
    HasFDerivAt ballScale ((-2 : ℝ) • innerSL ℝ q) q := by
  have hn : HasFDerivAt (Quaternion.normSq : ℍ → ℝ) ((2 : ℝ) • innerSL ℝ q) q := by
    simpa only [pow_two, ← Quaternion.normSq_eq_norm_mul_self, ← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_ofNat] using
      (hasStrictFDerivAt_norm_sq q).hasFDerivAt
  simpa only [ballScale, zero_sub, neg_smul] using! (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) q).sub hn

theorem ball_isOpen : IsOpen Ball :=
  isOpen_lt continuous_const (continuous_iff_continuousAt.mpr fun q => (hasFDerivAt_ballScale q).continuousAt)

/-- The second compact component of the connection one-form, evaluated on v. -/
def ballConnection (q v : ℍ) : ℍ := (ballScale q)⁻¹ • connectionCoefficient q v

theorem fderiv_ballConnection (q v w : ℍ) (hq : q ∈ Ball) :
    fderiv ℝ (fun x => ballConnection x w) q v =
      (2 * inner ℝ q v / ballScale q ^ 2) • connectionCoefficient q w +
      (ballScale q)⁻¹ • connectionCoefficient v w := by
  have hc := (((hasFDerivAt_id (𝕜 := ℝ) q).const_mul (star w)).sub
    (((hasFDerivAt_id (𝕜 := ℝ) q).star).mul_const' w)).const_smul ((2 : ℝ)⁻¹)
  have hd := ((hasFDerivAt_inv (ne_of_gt hq)).comp q (hasFDerivAt_ballScale q)).smul hc
  change HasFDerivAt (fun x => ballConnection x w) _ q at hd
  rw [hd.fderiv]
  simp [connectionCoefficient, innerSL_apply_apply, div_eq_mul_inv, smul_smul]
  module

/-- Curvature dA+A∧A, with dA evaluated on constant real vector fields. -/
def ballCurvature (q v w : ℍ) : ℍ :=
  fderiv ℝ (fun x => ballConnection x w) q v -
  fderiv ℝ (fun x => ballConnection x v) q w +
  (ballConnection q v * ballConnection q w - ballConnection q w * ballConnection q v)

/-- ξ_v is a quaternionic 2×2 matrix, not the quaternion v. -/
def tangentMatrix (v : ℍ) : QuaternionMatrix2 := !![0, v; star v, 0]

/-- The off-diagonal inclusion as a continuous real linear map. -/
def tangentCLM : ℍ →L[ℝ] QuaternionMatrix2 :=
  LinearMap.toContinuousLinearMap
    { toFun := tangentMatrix
      map_add' := by intros; apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> simp [tangentMatrix]
      map_smul' := by intros; apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> simp [tangentMatrix] }

@[simp] theorem tangentCLM_apply (v : ℍ) : tangentCLM v = tangentMatrix v := rfl

/-- The ball section σ(q)=(1-|q|²)^(-1/2)[[1,q],[conj(q),1]]. -/
def ballSection (q : ℍ) : QuaternionMatrix2 :=
  (Real.sqrt (ballScale q))⁻¹ • !![1, q; star q, 1]

/-- Explicit inverse, proved below on the ball. -/
def ballSectionInverse (q : ℍ) : QuaternionMatrix2 :=
  (Real.sqrt (ballScale q))⁻¹ • !![1, -q; -star q, 1]

theorem ballSection_inverse (q : ℍ) (hq : q ∈ Ball) :
    ballSectionInverse q * ballSection q = 1 ∧ ballSection q * ballSectionInverse q = 1 := by
  have hs : Real.sqrt (ballScale q) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hs2 := Real.sq_sqrt (le_of_lt hq)
  constructor <;> apply Matrix.ext <;> intro i j <;> fin_cases i <;> fin_cases j <;> apply Quaternion.ext <;>
    simp [ballSectionInverse, ballSection, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [hs]
  all_goals try rw [hs2]
  all_goals simp only [ballScale, Quaternion.normSq_def']
  all_goals ring_nf
  all_goals simp

/-- Differentiate the actual section, including the scalar square-root factor. -/
theorem fderiv_ballSection (q v : ℍ) (hq : q ∈ Ball) :
    fderiv ℝ ballSection q v =
      (inner ℝ q v / Real.sqrt (ballScale q) ^ 3) • !![1, q; star q, 1] +
      (Real.sqrt (ballScale q))⁻¹ • tangentMatrix v := by
  have hs : Real.sqrt (ballScale q) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hb : HasFDerivAt (fun x : ℍ => (!![1, x; star x, 1] : QuaternionMatrix2)) tangentCLM q := by
    convert! (hasFDerivAt_const (1 : QuaternionMatrix2) q).add tangentCLM.hasFDerivAt using 1
    · funext x; apply Matrix.ext; intro i j
      fin_cases i <;> fin_cases j <;> simp [tangentMatrix]
    · simp
  have hr : HasFDerivAt (fun x => (Real.sqrt (ballScale x))⁻¹) _ q :=
    (hasFDerivAt_inv hs).comp q ((hasFDerivAt_ballScale q).sqrt (ne_of_gt hq))
  have hd := hr.smul hb
  change HasFDerivAt ballSection _ q at hd
  rw [hd.fderiv]
  have hc : ((2 * Real.sqrt (ballScale q))⁻¹ * (-2 * inner ℝ q v)) * -(Real.sqrt (ballScale q) ^ 2)⁻¹ = inner ℝ q v / Real.sqrt (ballScale q) ^ 3 := by field_simp
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply, smul_eq_mul,
    tangentCLM_apply]
  rw [one_div, hc]
  exact add_comm _ _

/-- The complete Maurer–Cartan matrix L4, with the actual Fréchet derivative. -/
theorem ballSection_maurerCartan (q v : ℍ) (hq : q ∈ Ball) :
    ballSectionInverse q * fderiv ℝ ballSection q v =
      (ballScale q)⁻¹ • !![(2 : ℝ)⁻¹ • (v * star q - q * star v), v;
        star v, connectionCoefficient q v] := by
  rw [fderiv_ballSection q v hq]
  have hs : Real.sqrt (ballScale q) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hs2 := Real.sq_sqrt (le_of_lt hq)
  have hs0 : ballScale q ≠ 0 := ne_of_gt hq
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Quaternion.ext <;>
    simp [ballSectionInverse, tangentMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      connectionCoefficient, Quaternion.inner_def] <;>
    field_simp [hs, hs0] <;>
    simp only [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hs2] <;>
    simp [ballScale, Quaternion.normSq_def'] <;> ring_nf <;> simp

/-- The regularity hypotheses for the Maurer–Cartan equation on the ball. -/
theorem ballSections_contDiffAt_two (q : ℍ) (hq : q ∈ Ball) :
    ContDiffAt ℝ 2 ballSection q ∧ ContDiffAt ℝ 2 ballSectionInverse q := by
  have hs : ContDiff ℝ 2 ballScale := by
    have hn : ContDiff ℝ 2 (Quaternion.normSq : ℍ → ℝ) := by
      simpa only [id_eq, Quaternion.inner_self] using!
        (contDiff_id.inner ℝ contDiff_id : ContDiff ℝ 2 (fun x : ℍ => inner ℝ x x))
    exact contDiff_const.sub hn
  have hr := (hs.contDiffAt.sqrt (ne_of_gt hq)).inv (Real.sqrt_pos.mpr hq).ne'
  constructor
  · have hb : ContDiffAt ℝ 2 (fun x : ℍ => (1 : QuaternionMatrix2) + tangentCLM x) q :=
      contDiffAt_const.add tangentCLM.contDiff.contDiffAt
    convert! hr.smul hb using 1
    funext x
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j <;> simp [ballSection, tangentMatrix]
  · have hb : ContDiffAt ℝ 2 (fun x : ℍ => (1 : QuaternionMatrix2) - tangentCLM x) q :=
      contDiffAt_const.sub tangentCLM.contDiff.contDiffAt
    convert! hr.smul hb using 1
    funext x
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j <;> simp [ballSectionInverse, tangentMatrix]

/-- L6 is the lower-right block of Maurer–Cartan, using the full L4 form. -/
theorem ballCurvature_eq (q v w : ℍ) (hq : q ∈ Ball) :
    ballCurvature q v w = -(ballScale q)⁻¹ ^ 2 • (star v * w - star w * v) := by
  let θ (x u : ℍ) : QuaternionMatrix2 := ballSectionInverse x * fderiv ℝ ballSection x u
  let e : QuaternionMatrix2 →L[ℝ] ℍ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℍ) 1).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℍ) 1)
  have hf := (ballSections_contDiffAt_two q hq).1
  have hg := (ballSections_contDiffAt_two q hq).2.differentiableAt (by norm_num)
  have hgf : (fun x => ballSectionInverse x * ballSection x) =ᶠ[𝓝 q] fun _ => 1 := by
    filter_upwards [ball_isOpen.mem_nhds hq] with x hx
    exact (ballSection_inverse x hx).1
  have hmc := MathResearch.Analysis.maurerCartan hf hg hgf (ballSection_inverse q hq).2 v w
  change fderiv ℝ (fun x => θ x w) q v - fderiv ℝ (fun x => θ x v) q w +
    (θ q v * θ q w - θ q w * θ q v) = 0 at hmc
  have hd (u : ℍ) : DifferentiableAt ℝ (fun x => θ x u) q := by
    have hd2 : DifferentiableAt ℝ (fderiv ℝ ballSection) q :=
      (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    exact (MathResearch.Analysis.algebraMulCLM.hasFDerivAt_of_bilinear hg.hasFDerivAt
      (hd2.clm_apply (differentiableAt_const u)).hasFDerivAt).differentiableAt
  have he (u z : ℍ) : e (fderiv ℝ (fun x => θ x u) q z) =
      fderiv ℝ (fun x => ballConnection x u) q z := by
    have hlocal : (fun x => e (θ x u)) =ᶠ[𝓝 q] (fun x => ballConnection x u) := by
      filter_upwards [ball_isOpen.mem_nhds hq] with x hx
      change (ballSectionInverse x * fderiv ℝ ballSection x u) 1 1 = ballConnection x u
      rw [ballSection_maurerCartan x u hx]
      rfl
    have hder := (e.hasFDerivAt.comp q (hd u).hasFDerivAt).fderiv
    exact (congrArg (fun L : ℍ →L[ℝ] ℍ => L z) hder).symm.trans
      (congrArg (fun L : ℍ →L[ℝ] ℍ => L z) hlocal.fderiv_eq)
  have h := congrArg e hmc
  simp only [map_add, map_sub, map_zero, he] at h
  have hblock (u z : ℍ) : e (θ q u * θ q z) =
      (ballScale q)⁻¹ ^ 2 • (star u * z) + ballConnection q u * ballConnection q z := by
    change (θ q u * θ q z) 1 1 = _
    simp only [θ, ballSection_maurerCartan q u hq, ballSection_maurerCartan q z hq,
      Matrix.mul_apply, Fin.sum_univ_two]
    simp [ballConnection, smul_smul, pow_two]
  rw [hblock v w, hblock w v] at h
  unfold ballCurvature
  rw [neg_smul, smul_sub]
  apply eq_neg_of_add_eq_zero_left
  convert h using 1
  abel

/-- The curvature does not vanish even at the origin. -/
theorem ballCurvature_origin : ballCurvature 0 1 (⟨0, 1, 0, 0⟩ : ℍ) = ⟨0, -2, 0, 0⟩ := by
  rw [ballCurvature_eq _ _ _ (by simp [Ball, ballScale])]
  ext <;> norm_num [ballScale]

end MathResearch.Spinor
