module
public import MathResearch.Spinor.ClassicalRow

/-! An independent distributional row equation, compared with the image model.
The equation tests the actual quaternion coefficients of A-jB against ordinary
Lebesgue derivatives of compactly supported smooth tests. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion Distributions BigOperators
open MeasureTheory
namespace MathResearch.Spinor

def rowCoefficientCLM (m : ℕ) (d : Fin 2 →₀ ℕ) : CompatibleRow m →L[ℝ] ℍ :=
  (m+1:ℝ)⁻¹ • (fueterCoefficientCLM (m+1) d).comp
    ((spinorIsometry m).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)

theorem rowCoefficientCLM_apply (m : ℕ) (d : Fin 2 →₀ ℕ) (h : CompatibleRow m) :
    rowCoefficientCLM m d h = rowCoefficient m d h := by
  change (m+1:ℝ)⁻¹ • fueterCoefficientCLM (m+1) d ((spinorIsometry m).symm h) = _
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    (rowCoefficient_spinorIsometry m d ((spinorIsometry m).symm h)).symm

theorem compatibleBallL2_locallyIntegrableOn (m : ℕ) (hm : 1 ≤ m) (h : CompatibleBallL2 m) :
    LocallyIntegrableOn (fun q => h q) Ball volume := by
  obtain ⟨f, rfl⟩ := (spinorL2Isometry m).surjective h
  have he : (spinorL2Isometry m f : ℍ → CompatibleRow m) =ᵐ[volume.restrict Ball]
      (fun q => spinorIsometry m (f q)) :=
    (ae_weightedBall_iff (m+1) (by omega) _).mp
      (l2IsometryEquiv_ae (weightedBallMeasure (m+1)) (spinorIsometry m) f)
  exact ((spinorIsometry m).toContinuousLinearEquiv.toContinuousLinearMap.locallyIntegrableOn_comp
    (ballL2_locallyIntegrableOn (m+1) (by omega) f)).congr he.symm

theorem rowCoefficient_locallyIntegrableOn (m : ℕ) (hm : 1 ≤ m)
    (h : CompatibleBallL2 m) (d : Fin 2 →₀ ℕ) :
    LocallyIntegrableOn (fun q => rowCoefficient m d (h q)) Ball volume := by
  simpa only [Function.comp_def, rowCoefficientCLM_apply] using
    (rowCoefficientCLM m d).locallyIntegrableOn_comp (compatibleBallL2_locallyIntegrableOn m hm h)

def rowWeakTest (m : ℕ) (h : CompatibleBallL2 m) (φ : BallTest) (d : Fin 2 →₀ ℕ) : ℍ :=
  ∑ μ : Fin 4, Fueter.coordinateBasis μ *
    ∫ q in Ball, testDirectional (Fueter.coordinateBasis μ) φ q • rowCoefficient m d (h q)

/-- Independent weak form of D_l(A-jB)=0, coefficient by coefficient. -/
def RowDistributionRegular (m : ℕ) (h : CompatibleBallL2 m) : Prop :=
  ∀ φ d, rowWeakTest m h φ d = 0

/-- The test integral is the negative ordinary distributional Fueter derivative. -/
theorem rowWeakTest_eq_distribution (m : ℕ) (hm : 1 ≤ m) (h : CompatibleBallL2 m)
    (φ : BallTest) (d : Fin 2 →₀ ℕ) :
    rowWeakTest m h φ d = - ∑ μ : Fin 4, Fueter.coordinateBasis μ *
      (Distribution.lineDerivCLM (Fueter.coordinateBasis μ)
        (Distribution.ofFun ballOpen (fun q => rowCoefficient m d (h q)) volume ⊤)) φ := by
  simp only [Distribution.lineDerivCLM_apply, Distribution.ofFun_apply (Ω := ballOpen)
    (rowCoefficient_locallyIntegrableOn m hm h d), mul_neg, Finset.sum_neg_distrib, neg_neg]
  apply Finset.sum_congr rfl
  intro μ _
  congr 1
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun q hq => by
    change (testDirectional (Fueter.coordinateBasis μ) φ) q • rowCoefficient m d (h q) = 0
    rw [(testDirectional (Fueter.coordinateBasis μ) φ).zero_on_compl hq]
    simp

theorem integral_rowCoefficient_spinorL2 (m : ℕ) (hm : 1 ≤ m)
    (f : BallL2 (m+1)) (φ : BallTest) (d : Fin 2 →₀ ℕ) :
    (∫ q in Ball, φ q • rowCoefficient m d (spinorL2Isometry m f q)) =
      (m+1:ℝ)⁻¹ • fueterCoefficientCLM (m+1) d (spinorDistribution (m+1) f φ) := by
  have he := (ae_weightedBall_iff (m+1) (by omega) _).mp
    (l2IsometryEquiv_ae (weightedBallMeasure (m+1)) (spinorIsometry m) f)
  have hI : (∫ q in Ball, φ q • rowCoefficient m d (spinorL2Isometry m f q)) =
      (m+1:ℝ)⁻¹ • ∫ q in Ball, φ q • fueterCoefficientCLM (m+1) d (f q) := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [he] with q hq
    change spinorL2Isometry m f q = _ at hq
    rw [hq, rowCoefficient_spinorIsometry, smul_comm]
  rw [hI, spinorDistribution_apply (m+1) (by omega)]
  congr 1
  have hi := (φ.integrable_smul (ballL2_locallyIntegrableOn (m+1) (by omega) f)).integrableOn (s := Ball)
  simpa only [map_smul] using (fueterCoefficientCLM (m+1) d).integral_comp_comm hi

theorem pack_weakTest (n : ℕ) (hn : 2 ≤ n) (f : BallL2 n) (φ : BallTest) (d : Fin 2 →₀ ℕ) :
    pack (weakTest n hn φ 0 d f) (weakTest n hn φ 1 d f) =
      ∑ μ : Fin 4, Fueter.coordinateBasis μ *
        fueterCoefficientCLM n d (spinorDistribution n f (testDirectional (Fueter.coordinateBasis μ) φ)) := by
  rw [weakTest_distribution, weakTest_distribution, pack_sum]
  apply Finset.sum_congr rfl
  intro μ _
  exact matrixColumn_pack_coeff (Fueter.coordinateBasis μ)
    (fun i => MvPolynomial.pderiv i
      (spinorDistribution n f (testDirectional (Fueter.coordinateBasis μ) φ) : ComplexPoly2)) d

theorem rowWeakTest_spinorL2 (m : ℕ) (hm : 1 ≤ m) (f : BallL2 (m+1))
    (φ : BallTest) (d : Fin 2 →₀ ℕ) :
    rowWeakTest m (spinorL2Isometry m f) φ d =
      (m+1:ℝ)⁻¹ • pack (weakTest (m+1) (by omega) φ 0 d f) (weakTest (m+1) (by omega) φ 1 d f) := by
  simp only [rowWeakTest, integral_rowCoefficient_spinorL2 m hm,
    mul_smul_comm, ← Finset.smul_sum, pack_weakTest]

/-- The image-defined kernel agrees with the independently written distributional row PDE. -/
theorem mem_weakRowKernel_iff_distribution (m : ℕ) (hm : 1 ≤ m) (h : CompatibleBallL2 m) :
    h ∈ weakRowKernel m hm ↔ RowDistributionRegular m h := by
  obtain ⟨f, rfl⟩ := (spinorL2Isometry m).surjective h
  have hmap : spinorL2Isometry m f ∈ weakRowKernel m hm ↔ f ∈ weakKernel (m+1) (by omega) := by
    constructor
    · rintro ⟨g, hg, he⟩
      have hg' : g = f := (spinorL2Isometry m).injective he
      subst g
      exact hg
    · intro hf
      exact ⟨f, hf, rfl⟩
  rw [hmap, mem_weakKernel]
  constructor
  · intro hf φ d
    rw [rowWeakTest_spinorL2 m hm, hf φ 0 d, hf φ 1 d]
    simp [pack]
  · intro hf φ j d
    have hzero := hf φ d
    rw [rowWeakTest_spinorL2 m hm] at hzero
    have hp : pack (weakTest (m+1) (by omega) φ 0 d f) (weakTest (m+1) (by omega) φ 1 d f) = 0 :=
      (smul_eq_zero.mp hzero).resolve_left (inv_ne_zero (by positivity))
    have hpair : (weakTest (m+1) (by omega) φ 0 d f, weakTest (m+1) (by omega) φ 1 d f) = (0,0) :=
      pack_injective (by simpa [pack] using hp)
    fin_cases j
    · exact congrArg Prod.fst hpair
    · exact congrArg Prod.snd hpair

end MathResearch.Spinor
