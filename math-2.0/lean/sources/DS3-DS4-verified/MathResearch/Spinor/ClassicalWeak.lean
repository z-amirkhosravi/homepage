module
public import MathResearch.Spinor.WeylRegularity

/-! Equality of the distributional and classical Fueter kernels, with a.e.
representatives and polynomial coefficient conventions made explicit. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion ContDiff Distributions BigOperators
open MeasureTheory InnerProductSpace
namespace MathResearch.Spinor

/-- The two complex coefficient equations of the classical polynomial-spinor operator. -/
def classicalSymbol (n : ℕ) (F : ℍ → BinaryForm n) (j : Fin 2) (d : Fin 2 →₀ ℕ) (q : ℍ) : ℂ :=
  ∑ μ : Fin 4, weakSymbol n μ j d (fderiv ℝ F q (Fueter.coordinateBasis μ))

theorem contDiffOn_classicalSymbol (n : ℕ) {F : ℍ → BinaryForm n}
    (hF : ContDiffOn ℝ ∞ F Ball) (j : Fin 2) (d : Fin 2 →₀ ℕ) :
    ContDiffOn ℝ ∞ (classicalSymbol n F j d) Ball :=
  ContDiffOn.sum (fun μ _ => ((weakSymbol n μ j d).restrictScalars ℝ).contDiff.comp_contDiffOn
    (contDiffOn_directional hF _))

theorem pack_classicalSymbol (n : ℕ) {F : ℍ → BinaryForm n} {q : ℍ}
    (hF : DifferentiableAt ℝ F q) (d : Fin 2 →₀ ℕ) :
    pack (classicalSymbol n F 0 d q) (classicalSymbol n F 1 d q) =
      Fueter.leftOperator (fun x => fueterCoefficientCLM n d (F x)) q := by
  have hd := (fueterCoefficientCLM n d).hasFDerivAt.comp q hF.hasFDerivAt
  change HasFDerivAt (fun x => fueterCoefficientCLM n d (F x)) _ q at hd
  rw [Fueter.leftOperator_eq]
  simp only [classicalSymbol, pack_sum, Fueter.coordPartial, Fueter.directional, hd.fderiv,
    ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro μ _
  exact matrixColumn_pack_coeff (Fueter.coordinateBasis μ)
    (fun i => MvPolynomial.pderiv i (fderiv ℝ F q (Fueter.coordinateBasis μ) : ComplexPoly2)) d

theorem weakTest_eq_integral_classicalSymbol (n : ℕ) (hn : 2 ≤ n)
    (f : BallL2 n) {F : ℍ → BinaryForm n} (hF : ContDiffOn ℝ ∞ F Ball)
    (he : (f : ℍ → BinaryForm n) =ᵐ[weightedBallMeasure n] F)
    (φ : BallTest) (j : Fin 2) (d : Fin 2 →₀ ℕ) :
    weakTest n hn φ j d f = - ∫ x, φ x • classicalSymbol n F j d x := by
  have hi := hF.continuousOn.locallyIntegrableOn (μ := volume) ball_isOpen.measurableSet
  have hdist : spinorDistribution n f = Distribution.ofFun ballOpen F volume ⊤ :=
    Distribution.ofFun_congr_ae ((ae_weightedBall_iff n hn _).mp he)
  rw [weakTest_distribution, hdist]
  have H (μ : Fin 4) : weakSymbol n μ j d
      (Distribution.ofFun ballOpen F volume ⊤ (testDirectional (Fueter.coordinateBasis μ) φ)) =
      - ∫ x, φ x • weakSymbol n μ j d (fderiv ℝ F x (Fueter.coordinateBasis μ)) := by
    rw [Distribution.ofFun_apply hi]
    have hp := integral_test_directional hF (Fueter.coordinateBasis μ) φ
    have hp' : (∫ x, testDirectional (Fueter.coordinateBasis μ) φ x • F x) =
        - ∫ x, φ x • fderiv ℝ F x (Fueter.coordinateBasis μ) := by
      simpa only [neg_neg] using congrArg Neg.neg hp.symm
    rw [hp', map_neg]
    congr 1
    have hd := (contDiffOn_directional hF (Fueter.coordinateBasis μ)).continuousOn.locallyIntegrableOn
      (μ := volume) ball_isOpen.measurableSet
    simpa only [map_smul, ContinuousLinearMap.coe_restrictScalars'] using
      (((weakSymbol n μ j d).restrictScalars ℝ).integral_comp_comm (φ.integrable_smul hd)).symm
  simp_rw [H]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum]
  · congr 1
    apply integral_congr_ae
    filter_upwards with x
    simp only [classicalSymbol, Finset.smul_sum]
  · intro μ _
    have hc : ContDiffOn ℝ ∞ (fun x => weakSymbol n μ j d (fderiv ℝ F x (Fueter.coordinateBasis μ))) Ball :=
      ((weakSymbol n μ j d).restrictScalars ℝ).contDiff.comp_contDiffOn
        (contDiffOn_directional hF _)
    exact φ.integrable_smul (hc.continuousOn.locallyIntegrableOn ball_isOpen.measurableSet)

/-- Pointwise classical equations characterize membership of a smooth representative's L² class. -/
theorem mem_weakKernel_iff_classicalSymbol (n : ℕ) (hn : 2 ≤ n)
    (f : BallL2 n) {F : ℍ → BinaryForm n} (hF : ContDiffOn ℝ ∞ F Ball)
    (he : (f : ℍ → BinaryForm n) =ᵐ[weightedBallMeasure n] F) :
    f ∈ weakKernel n hn ↔ ∀ q ∈ Ball, ∀ j d, classicalSymbol n F j d q = 0 := by
  constructor
  · intro hf q hq j d
    have hc := (contDiffOn_classicalSymbol n hF j d).continuousOn
    have hi := hc.locallyIntegrableOn (μ := volume) ball_isOpen.measurableSet
    have hz : Distribution.ofFun ballOpen (classicalSymbol n F j d) volume ⊤ = 0 := by
      ext φ : 1
      rw [Distribution.ofFun_apply hi]
      have hh := (mem_weakKernel n hn f).mp hf φ j d
      rw [weakTest_eq_integral_classicalSymbol n hn f hF he] at hh
      simpa using hh
    have hae := Distribution.ofFun_injective hi locallyIntegrableOn_zero
      (hz.trans (Distribution.ofFun_zero).symm)
    exact Measure.eqOn_open_of_ae_eq hae ball_isOpen hc continuousOn_const hq
  · intro h
    rw [mem_weakKernel]
    intro φ j d
    rw [weakTest_eq_integral_classicalSymbol n hn f hF he]
    suffices (∫ x, φ x • classicalSymbol n F j d x) = 0 by exact neg_eq_zero.mpr this
    apply integral_eq_zero_of_ae
    filter_upwards with x
    by_cases hx : x ∈ Ball
    · simp [h x hx j d]
    · simp [φ.zero_on_compl hx]

/-- Exact equivalence with the quaternionic Fueter equation used by SC3. -/
theorem mem_weakKernel_iff_classicalFueter (n : ℕ) (hn : 2 ≤ n)
    (f : BallL2 n) {F : ℍ → BinaryForm n} (hF : ContDiffOn ℝ ∞ F Ball)
    (he : (f : ℍ → BinaryForm n) =ᵐ[weightedBallMeasure n] F) :
    f ∈ weakKernel n hn ↔ ∀ q ∈ Ball, ∀ d,
      Fueter.leftOperator (fun x => fueterCoefficientCLM n d (F x)) q = 0 := by
  rw [mem_weakKernel_iff_classicalSymbol n hn f hF he]
  constructor
  · intro h q hq d
    rw [← pack_classicalSymbol n
      (((hF q hq).contDiffAt (ball_isOpen.mem_nhds hq)).differentiableAt (by simp)),
      h q hq 0 d, h q hq 1 d]
    simp [pack]
  · intro h q hq j d
    have hp : pack (classicalSymbol n F 0 d q) (classicalSymbol n F 1 d q) = pack 0 0 := by
      rw [pack_classicalSymbol n
        (((hF q hq).contDiffAt (ball_isOpen.mem_nhds hq)).differentiableAt (by simp)), h q hq d]
      simp [pack]
    have hh : (classicalSymbol n F 0 d q, classicalSymbol n F 1 d q) = (0, 0) := pack_injective hp
    fin_cases j
    · exact congrArg Prod.fst hh
    · exact congrArg Prod.snd hh

/-- Every weak vector has a smooth representative satisfying the actual classical equation. -/
theorem weakKernel_classicalRepresentative (n : ℕ) (hn : 2 ≤ n) (f : WeakBallSpace n hn) :
    ∃ F : ℍ → BinaryForm n, ContDiffOn ℝ ∞ F Ball ∧
      (∀ q ∈ Ball, ∀ d, Fueter.leftOperator (fun x => fueterCoefficientCLM n d (F x)) q = 0) ∧
      (f.val : ℍ → BinaryForm n) =ᵐ[weightedBallMeasure n] F := by
  obtain ⟨F, hF, _, he⟩ := weakKernel_smoothRepresentative n hn f
  exact ⟨F, hF, (mem_weakKernel_iff_classicalFueter n hn f.val hF he).mp f.property, he⟩

end MathResearch.Spinor
