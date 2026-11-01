module
public import MathResearch.Spinor.RegularAction
public import MathResearch.Spinor.WeakRowSpace

/-! The smooth row model is specified independently by its fibre constraint
and classical coefficientwise Fueter equation, then identified with the weak model. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion ContDiff
open MeasureTheory
namespace MathResearch.Spinor

/-- Coefficient of A-jB in the actual compatible row (A,B), for any monomial. -/
def rowCoefficient (m : ℕ) (d : Fin 2 →₀ ℕ) (h : CompatibleRow m) : ℍ :=
  pack ((h.val 0 : ComplexPoly2).coeff d) ((h.val 1 : ComplexPoly2).coeff d)

theorem rowCoefficient_spinorIsometry (m : ℕ) (d : Fin 2 →₀ ℕ) (p : BinaryForm (m+1)) :
    rowCoefficient m d (spinorIsometry m p) = (m + 1 : ℝ)⁻¹ • fueterCoefficientCLM (m+1) d p := by
  change pack (((m+1:ℂ)⁻¹ • MvPolynomial.pderiv 0 (p : ComplexPoly2)).coeff d)
    (((m+1:ℂ)⁻¹ • MvPolynomial.pderiv 1 (p : ComplexPoly2)).coeff d) = _
  simp only [MvPolynomial.coeff_smul, smul_eq_mul, fueterCoefficientCLM_apply, polynomialFueterCoefficients]
  have hr : ((m+1:ℝ)⁻¹ : ℂ) = (m+1:ℂ)⁻¹ := by simp
  rw [← hr]
  simpa only [Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one] using
    (pack_real_smul (m+1:ℝ)⁻¹ (((MvPolynomial.pderiv 0) (p : ComplexPoly2)).coeff d)
      (((MvPolynomial.pderiv 1) (p : ComplexPoly2)).coeff d))

theorem leftOperator_real_smul (r : ℝ) {F : ℍ → ℍ} {q : ℍ} (hF : DifferentiableAt ℝ F q) :
    Fueter.leftOperator (fun x => r • F x) q = r • Fueter.leftOperator F q := by
  simp only [Fueter.leftOperator, fderiv_fun_const_smul hF, map_smul]

theorem row_fueter_iff (m : ℕ) {F : ℍ → BinaryForm (m+1)}
    (hF : ContDiffOn ℝ ∞ F Ball) :
    (∀ q ∈ Ball, ∀ d, Fueter.leftOperator (fun x => rowCoefficient m d (spinorIsometry m (F x))) q = 0) ↔
      (∀ q ∈ Ball, ∀ d, Fueter.leftOperator (fun x => fueterCoefficientCLM (m+1) d (F x)) q = 0) := by
  have H (q : ℍ) (hq : q ∈ Ball) (d : Fin 2 →₀ ℕ) :
      Fueter.leftOperator (fun x => rowCoefficient m d (spinorIsometry m (F x))) q =
        (m+1:ℝ)⁻¹ • Fueter.leftOperator (fun x => fueterCoefficientCLM (m+1) d (F x)) q := by
    simp_rw [rowCoefficient_spinorIsometry]
    apply leftOperator_real_smul
    exact (fueterCoefficientCLM (m+1) d).differentiableAt.comp q
      (((hF q hq).contDiffAt (ball_isOpen.mem_nhds hq)).differentiableAt (by simp))
  constructor
  · intro h q hq d
    have hd := h q hq d
    rw [H q hq d] at hd
    exact (smul_eq_zero.mp hd).resolve_left (inv_ne_zero (by positivity))
  · intro h q hq d
    rw [H q hq d, h q hq d, smul_zero]

/-- Independently specified smooth compatible-row realization inside its actual L² space.
Compatibility is built into CompatibleRow; regularity is imposed on A-jB's coefficients. -/
def HasClassicalRowRepresentative (m : ℕ) (h : CompatibleBallL2 m) : Prop :=
  ∃ H : ℍ → CompatibleRow m, ContDiffOn ℝ ∞ H Ball ∧
    (∀ q ∈ Ball, ∀ d, Fueter.leftOperator (fun x => rowCoefficient m d (H x)) q = 0) ∧
    (h : ℍ → CompatibleRow m) =ᵐ[weightedBallMeasure (m+1)] H

/-- The old image-defined weak row model equals the independently stated smooth row model. -/
theorem mem_weakRowKernel_iff_classical (m : ℕ) (hm : 1 ≤ m) (h : CompatibleBallL2 m) :
    h ∈ weakRowKernel m hm ↔ HasClassicalRowRepresentative m h := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨F, hF, hD, he⟩ := weakKernel_classicalRepresentative (m+1) (by omega) ⟨f, hf⟩
    refine ⟨fun q => spinorIsometry m (F q),
      ((spinorIsometry m).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp_contDiffOn hF,
      (row_fueter_iff m hF).mpr hD, ?_⟩
    filter_upwards [l2IsometryEquiv_ae (weightedBallMeasure (m+1)) (spinorIsometry m) f, he] with q hq hFq
    change (l2IsometryEquiv (weightedBallMeasure (m+1)) (spinorIsometry m) f) q = _
    rw [hq, hFq]
  · rintro ⟨H, hH, hD, he⟩
    let f := (spinorL2Isometry m).symm h
    let F : ℍ → BinaryForm (m+1) := fun q => (spinorIsometry m).symm (H q)
    have hF : ContDiffOn ℝ ∞ F Ball :=
      ((spinorIsometry m).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp_contDiffOn hH
    have ha : (f : ℍ → BinaryForm (m+1)) =ᵐ[weightedBallMeasure (m+1)] F := by
      have hh := l2IsometryEquiv_ae (weightedBallMeasure (m+1)) (spinorIsometry m) f
      change (spinorL2Isometry m f : ℍ → CompatibleRow m) =ᵐ[_] _ at hh
      rw [show spinorL2Isometry m f = h from (spinorL2Isometry m).apply_symm_apply h] at hh
      filter_upwards [hh, he] with q hq heq
      apply (spinorIsometry m).injective
      change spinorIsometry m (f q) = spinorIsometry m ((spinorIsometry m).symm (H q))
      rw [LinearIsometryEquiv.apply_symm_apply]
      exact hq.symm.trans heq
    have hp : ∀ q ∈ Ball, ∀ d,
        Fueter.leftOperator (fun x => fueterCoefficientCLM (m+1) d (F x)) q = 0 := by
      apply (row_fueter_iff m hF).mp
      simpa only [F, LinearIsometryEquiv.apply_symm_apply] using hD
    have hf := (mem_weakKernel_iff_classicalFueter (m+1) (by omega) f hF ha).mpr hp
    exact ⟨f, hf, (spinorL2Isometry m).apply_symm_apply h⟩

end MathResearch.Spinor
