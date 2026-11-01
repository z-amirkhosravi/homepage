module
public import MathResearch.Spinor.WeightedLocalization
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-! The first step of the written DS2 regularity argument: conjugate Fueter
factorization on actual mathlib distributions. No Weyl lemma is assumed here. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Quaternion BigOperators Distributions ContDiff
open MeasureTheory
namespace MathResearch.Spinor

def testDirectional (v : ℍ) : BallTest →L[ℝ] BallTest := TestFunction.lineDerivCLM ℝ v

@[simp] theorem testDirectional_apply (v : ℍ) (φ : BallTest) (q : ℍ) :
    testDirectional v φ q = fderiv ℝ φ q v := by
  rw [testDirectional, TestFunction.lineDerivCLM_apply_of_le (by simp)]
  exact (φ.contDiff.differentiable (by simp) q).lineDeriv_eq_fderiv

theorem testDirectional_comm (v w : ℍ) (φ : BallTest) :
    testDirectional v (testDirectional w φ) = testDirectional w (testDirectional v φ) := by
  apply TestFunction.ext
  intro q
  simp only [testDirectional_apply]
  have he (u : ℍ) : (⇑(testDirectional u φ) : ℍ → ℝ) = fun x => fderiv ℝ φ x u := by
    funext x; exact testDirectional_apply u φ x
  rw [he w, he v]
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) q :=
    (φ.contDiff.fderiv_right (m := ∞) (by simp)).differentiable (by simp) q
  rw [fderiv_clm_apply hd (differentiableAt_const w),
    fderiv_clm_apply hd (differentiableAt_const v)]
  simpa using (φ.contDiff.contDiffAt.isSymmSndFDerivAt (by simp)).eq v w

/-- The sum of the four ordinary second coordinate derivatives of a test. -/
def testLaplacian (φ : BallTest) : BallTest :=
  ∑ μ : Fin 4, testDirectional (Fueter.coordinateBasis μ)
    (testDirectional (Fueter.coordinateBasis μ) φ)

/-- Our test-function Laplacian is mathlib's Euclidean Laplacian, in the
already verified orthonormal quaternion basis. -/
theorem testLaplacian_eq (φ : BallTest) :
    (⇑(testLaplacian φ) : ℍ → ℝ) = Laplacian.laplacian (⇑φ : ℍ → ℝ) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ quaternionONB]
  funext q
  simp only [testLaplacian, FunLike.coe_sum, Finset.sum_apply,
    testDirectional_apply, iteratedFDeriv_two_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, quaternionONB_apply]
  apply Finset.sum_congr rfl
  intro μ _
  have he : (⇑(testDirectional (Fueter.coordinateBasis μ) φ) : ℍ → ℝ) =
      fun x => fderiv ℝ φ x (Fueter.coordinateBasis μ) := by
    funext x; exact testDirectional_apply _ φ x
  rw [he, fderiv_clm_apply
    ((φ.contDiff.fderiv_right (m := ∞) (by simp)).differentiable (by simp) q)
    (differentiableAt_const _)]
  simp

/-- The Laplacian on distributions is the sum of mathlib distribution derivatives. -/
def distributionLaplacian {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : 𝓓'(ballOpen, F)) : 𝓓'(ballOpen, F) :=
  ∑ μ : Fin 4, Distribution.lineDerivCLM (k := ⊤) (Fueter.coordinateBasis μ)
    (Distribution.lineDerivCLM (Fueter.coordinateBasis μ) T)

theorem distributionLaplacian_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : 𝓓'(ballOpen, F)) (φ : BallTest) :
    distributionLaplacian T φ = T (testLaplacian φ) := by
  simp [distributionLaplacian, Distribution.lineDerivCLM_apply,
    testLaplacian, testDirectional]

theorem weakTest_distribution (n : ℕ) (hn : 2 ≤ n) (φ : BallTest)
    (j : Fin 2) (d : Fin 2 →₀ ℕ) (f : BallL2 n) :
    weakTest n hn φ j d f = ∑ μ : Fin 4,
      weakSymbol n μ j d (spinorDistribution n f (testDirectional (Fueter.coordinateBasis μ) φ)) := by
  have hi (μ : Fin 4) : IntegrableOn
      (fun q => testDirectional (Fueter.coordinateBasis μ) φ q • f q) Ball volume :=
    ((testDirectional (Fueter.coordinateBasis μ) φ).integrable_smul
      (ballL2_locallyIntegrableOn n hn f)).integrableOn
  have his (μ : Fin 4) : IntegrableOn
      (fun q => (fderiv ℝ φ q (Fueter.coordinateBasis μ) : ℂ) * weakSymbol n μ j d (f q)) Ball := by
    change Integrable _ (volume.restrict Ball)
    simpa [Complex.real_smul] using ((weakSymbol n μ j d).restrictScalars ℝ).integrable_comp (hi μ)
  rw [← Lp.toLp_coeFn f (Lp.memLp f), weakTest_toLp]
  simp only [Lp.toLp_coeFn]
  rw [integral_finsetSum _ (fun μ _ => his μ)]
  apply Finset.sum_congr rfl
  intro μ _
  rw [spinorDistribution_apply n hn]
  simpa [Complex.real_smul] using
    ((weakSymbol n μ j d).restrictScalars ℝ).integral_comp_comm (hi μ)

/-- The weak polynomial test equations are the coefficientwise quaternion Fueter equation. -/
theorem weakKernel_distribution_fueter (n : ℕ) (hn : 2 ≤ n) (f : WeakBallSpace n hn)
    (φ : BallTest) (d : Fin 2 →₀ ℕ) :
    (∑ μ : Fin 4, Fueter.coordinateBasis μ * fueterCoefficientCLM n d
      (spinorDistribution n f.val (testDirectional (Fueter.coordinateBasis μ) φ))) = 0 := by
  have h (j : Fin 2) := (mem_weakKernel n hn f.val).mp f.property φ j d
  simp only [weakTest_distribution] at h
  have hh := congrArg₂ pack (h 0) (h 1)
  have hpack (μ : Fin 4) (p : BinaryForm n) :
      pack (weakSymbol n μ 0 d p) (weakSymbol n μ 1 d p) =
        Fueter.coordinateBasis μ * fueterCoefficientCLM n d p := by
    change pack ((matrixColumn (quaternionMatrix (Fueter.coordinateBasis μ))
      (fun i => MvPolynomial.pderiv i (p : ComplexPoly2)) 0).coeff d)
      ((matrixColumn (quaternionMatrix (Fueter.coordinateBasis μ))
      (fun i => MvPolynomial.pderiv i (p : ComplexPoly2)) 1).coeff d) =
      Fueter.coordinateBasis μ * pack ((MvPolynomial.pderiv 0 (p : ComplexPoly2)).coeff d)
        ((MvPolynomial.pderiv 1 (p : ComplexPoly2)).coeff d)
    exact matrixColumn_pack_coeff _ _ d
  simpa only [pack_sum, hpack, show pack 0 0 = 0 by simp [pack]] using hh

/-- Algebraic Clifford cancellation, with the symmetry of second derivatives explicit. -/
theorem quaternion_laplacian_contraction (S : Fin 4 → Fin 4 → ℍ)
    (hs : ∀ μ ν, S μ ν = S ν μ) :
    (∑ ν : Fin 4, star (Fueter.coordinateBasis ν) *
      (∑ μ : Fin 4, Fueter.coordinateBasis μ * S ν μ)) = ∑ μ : Fin 4, S μ μ := by
  simp only [Fin.sum_univ_four]
  rw [hs 1 0, hs 2 0, hs 3 0, hs 2 1, hs 3 1, hs 3 2]
  ext <;> simp [Fueter.coordinateBasis_eq] <;> ring

theorem fueterCoefficient_jointly_injective (n : ℕ) (hn : 0 < n) (p : BinaryForm n)
    (hp : ∀ d, fueterCoefficientCLM n d p = 0) : p = 0 := by
  have hz (i : Fin 2) : MvPolynomial.pderiv i (p : ComplexPoly2) = 0 := by
    ext d
    have hh : (((MvPolynomial.pderiv 0 (p : ComplexPoly2)).coeff d),
        ((MvPolynomial.pderiv 1 (p : ComplexPoly2)).coeff d)) = (0, 0) := by
      apply pack_injective
      simpa [fueterCoefficientCLM_apply, polynomialFueterCoefficients, pack] using hp d
    fin_cases i
    · exact congrArg Prod.fst hh
    · exact congrArg Prod.snd hh
  have he := euler_homogeneous n p
  simp only [euler, hz, mul_zero, zero_add] at he
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hp' : (p : ComplexPoly2) = 0 := (smul_eq_zero.mp he.symm).resolve_left hn'
  exact Subtype.ext hp'

/-- Every actual weighted weak solution has zero distributional Laplacian.
This is the factorization/injectivity step of DS2, before Weyl regularity. -/
theorem weakKernel_distribution_harmonic (n : ℕ) (hn : 2 ≤ n) (f : WeakBallSpace n hn)
    (φ : BallTest) : spinorDistribution n f.val (testLaplacian φ) = 0 := by
  apply fueterCoefficient_jointly_injective n (by omega)
  intro d
  let S : Fin 4 → Fin 4 → ℍ := fun ν μ => fueterCoefficientCLM n d
    (spinorDistribution n f.val (testDirectional (Fueter.coordinateBasis μ)
      (testDirectional (Fueter.coordinateBasis ν) φ)))
  have hs : ∀ μ ν, S μ ν = S ν μ := by
    intro μ ν
    dsimp [S]
    rw [testDirectional_comm]
  have hh := quaternion_laplacian_contraction S hs
  have hz (ν : Fin 4) : (∑ μ : Fin 4, Fueter.coordinateBasis μ * S ν μ) = 0 :=
    weakKernel_distribution_fueter n hn f (testDirectional (Fueter.coordinateBasis ν) φ) d
  rw [show (∑ ν : Fin 4, star (Fueter.coordinateBasis ν) *
    (∑ μ : Fin 4, Fueter.coordinateBasis μ * S ν μ)) = 0 by simp [hz]] at hh
  simpa only [testLaplacian, map_sum, S] using hh.symm

theorem weakKernel_distributionLaplacian_zero (n : ℕ) (hn : 2 ≤ n)
    (f : WeakBallSpace n hn) : distributionLaplacian (spinorDistribution n f.val) = 0 := by
  ext φ : 1
  simpa only [distributionLaplacian_apply, zero_apply] using
    weakKernel_distribution_harmonic n hn f φ

end MathResearch.Spinor
