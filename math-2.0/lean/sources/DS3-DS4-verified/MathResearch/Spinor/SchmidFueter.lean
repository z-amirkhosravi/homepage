module
public import MathResearch.Spinor.FrameLift
public import MathResearch.Spinor.WeightedFueter

/-! SC1 and SC3: the moving-frame and weighted Schmid–Fueter identities. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion BigOperators Matrix.Norms.Elementwise
open MvPolynomial
namespace MathResearch.Spinor

/-- Each coefficient of the unnormalized T_n=p_X-jp_Y is real continuous linear. -/
def fueterCoefficientCLM (n : ℕ) (d : Fin 2 →₀ ℕ) : BinaryForm n →L[ℝ] ℍ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => polynomialFueterCoefficients p d
      map_add' := by intros; simp [polynomialFueterCoefficients, pack_add]
      map_smul' := by
        intro r p
        change polynomialFueterCoefficients ((r : ℂ) • (p : ComplexPoly2)) d = r • polynomialFueterCoefficients p d
        simpa [polynomialFueterCoefficients] using
          pack_real_smul r ((pderiv 0 (p : ComplexPoly2)).coeff d) ((pderiv 1 (p : ComplexPoly2)).coeff d) }

@[simp] theorem fueterCoefficientCLM_apply (n : ℕ) (d : Fin 2 →₀ ℕ) (p : BinaryForm n) :
    fueterCoefficientCLM n d p = polynomialFueterCoefficients p d := rfl

/-- 24 times the normalized projected operator, with all polynomial coefficients retained. -/
def projectedGroupOperator (n : ℕ) (F : QuaternionMatrix2 → BinaryForm n)
    (g : QuaternionMatrix2) (d : Fin 2 →₀ ℕ) : ℍ :=
  ∑ μ : Fin 4, Fueter.coordinateBasis μ *
    fueterCoefficientCLM n d (rightLieDerivative n F g (Fueter.coordinateBasis μ))

def schmidOperator (n : ℕ) (F : QuaternionMatrix2 → BinaryForm n)
    (g : QuaternionMatrix2) (d : Fin 2 →₀ ℕ) : ℍ := (24 : ℝ)⁻¹ • projectedGroupOperator n F g d

theorem schmidOperator_normalization (n : ℕ) (F : QuaternionMatrix2 → BinaryForm n)
    (g : QuaternionMatrix2) (d : Fin 2 →₀ ℕ) :
    (24 : ℝ) • schmidOperator n F g d = projectedGroupOperator n F g d := by
  simp [schmidOperator, smul_smul]

/-- Projection of the verified moving-frame derivative, with the SC2 term included. -/
theorem projectedGroupOperator_section (m : ℕ) (U : ℍ → BinaryForm (m+1)) (q : ℍ)
    (hq : q ∈ Ball) (hU : DifferentiableAt ℝ U q) (d : Fin 2 →₀ ℕ) :
    projectedGroupOperator (m+1) (frameLift (m+1) U) (ballSection q) d =
      ballScale q • Fueter.leftOperator (fun x => fueterCoefficientCLM (m+1) d (U x)) q +
      (m+3 : ℝ) • (q * fueterCoefficientCLM (m+1) d (U q)) := by
  have hd := (fueterCoefficientCLM (m+1) d).hasFDerivAt.comp q hU.hasFDerivAt
  change HasFDerivAt (fun x => fueterCoefficientCLM (m+1) d (U x)) _ q at hd
  have hc := congrFun (SC2_v1 (m+1) (by omega) q (U q)).2 d
  simp only [Nat.cast_add, Nat.cast_one] at hc
  rw [projectedGroupOperator, Fueter.leftOperator_eq]
  simp only [SC1_frame_v1 m U q _ hq hU, map_add, map_smul,
    mul_add, mul_smul_comm, Finset.sum_add_distrib, ← Finset.smul_sum]
  have hfirst : (∑ μ : Fin 4, Fueter.coordinateBasis μ *
      fueterCoefficientCLM (m+1) d (fderiv ℝ U q (Fueter.coordinateBasis μ))) =
      ∑ μ : Fin 4, Fueter.coordinateBasis μ *
        Fueter.coordPartial μ (fun x => fueterCoefficientCLM (m+1) d (U x)) q := by
    simp only [Fueter.coordPartial, Fueter.directional, hd.fderiv, ContinuousLinearMap.comp_apply]
  rw [hfirst]
  congr 1
  simpa only [fueterCoefficientCLM_apply, infinitesimalAction, LinearMap.coe_mk, AddHom.coe_mk,
    show (m:ℝ)+1+2 = m+3 by ring] using hc

/-- SC1/v1: the actual section connection, curvature and changing-frame formula. -/
theorem SC1_section_v1 (m : ℕ) (U : ℍ → BinaryForm (m+1)) (q : ℍ)
    (hq : q ∈ Ball) (hU : DifferentiableAt ℝ U q) :
    (∀ v, ballSectionInverse q * fderiv ℝ ballSection q v =
      (ballScale q)⁻¹ • !![(2:ℝ)⁻¹ • (v * star q - q * star v), v;
        star v, connectionCoefficient q v]) ∧
    (∀ v w, ballCurvature q v w = -(ballScale q)⁻¹ ^ 2 • (star v * w - star w * v)) ∧
    (∀ v, rightLieDerivative (m+1) (frameLift (m+1) U) (ballSection q) v =
      ballScale q • fderiv ℝ U q v + infinitesimalAction m (quaternionMatrix (connectionCoefficient q v)) (U q)) :=
  ⟨fun v => ballSection_maurerCartan q v hq, fun v w => ballCurvature_eq q v w hq,
    fun v => SC1_frame_v1 m U q v hq hU⟩

/-- The section data corresponding to the ball spinor f, with the exact positive real power. -/
def weightedSpinor (n : ℕ) (f : ℍ → BinaryForm n) (q : ℍ) : BinaryForm n :=
  ballWeight (((n:ℝ)+2)/2) q • f q

/-- The exact weighted identity, with n=m+1, at every polynomial exponent. -/
theorem SC3_v1_coefficients (m : ℕ) (f : ℍ → BinaryForm (m+1)) (q : ℍ)
    (hq : q ∈ Ball) (hf : DifferentiableAt ℝ f q) (d : Fin 2 →₀ ℕ) :
    projectedGroupOperator (m+1) (frameLift (m+1) (weightedSpinor (m+1) f)) (ballSection q) d =
      ballWeight ((((m+1:ℕ):ℝ)+4)/2) q •
        Fueter.leftOperator (fun x => fueterCoefficientCLM (m+1) d (f x)) q := by
  have hU : DifferentiableAt ℝ (weightedSpinor (m+1) f) q :=
    ((hasFDerivAt_ballWeight _ hq).smul hf.hasFDerivAt).differentiableAt
  rw [projectedGroupOperator_section m _ q hq hU]
  simpa only [weightedSpinor, map_smul, Nat.cast_add, Nat.cast_one,
    show (m:ℝ)+1+2 = m+3 by ring] using
      weighted_fueter_cancellation (m+1) (fun x => fueterCoefficientCLM (m+1) d (f x)) hq
        ((fueterCoefficientCLM (m+1) d).differentiableAt.comp q hf)

end MathResearch.Spinor
