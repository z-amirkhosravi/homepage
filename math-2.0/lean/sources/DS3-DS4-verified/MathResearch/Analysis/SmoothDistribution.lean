module
public import MathResearch.Analysis.RadialLaplacian
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! Classical derivatives and distribution derivatives agree on the open ball.
All integration-by-parts factors are explicitly proved integrable. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion ContDiff Topology Distributions BigOperators
open MeasureTheory InnerProductSpace Filter
namespace MathResearch.Spinor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffOn_directional {u : ℍ → E} (hu : ContDiffOn ℝ ∞ u Ball) (v : ℍ) :
    ContDiffOn ℝ ∞ (fun x => fderiv ℝ u x v) Ball :=
  (hu.fderiv_of_isOpen ball_isOpen (m := ∞) (by simp)).clm_apply contDiffOn_const

theorem integral_test_directional {u : ℍ → E} (hu : ContDiffOn ℝ ∞ u Ball)
    (v : ℍ) (φ : BallTest) :
    ∫ x, φ x • fderiv ℝ u x v = - ∫ x, testDirectional v φ x • u x := by
  have hi := hu.continuousOn.locallyIntegrableOn (μ := volume) ball_isOpen.measurableSet
  have hi' := (contDiffOn_directional hu v).continuousOn.locallyIntegrableOn (μ := volume) ball_isOpen.measurableSet
  have hf'g : Integrable (fun x => fderiv ℝ φ x v • u x) := by
    simpa only [testDirectional_apply] using (testDirectional v φ).integrable_smul hi
  exact integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable hf'g (φ.integrable_smul hi')
    (φ.integrable_smul hi) (fun x _ => φ.contDiff.differentiable (by simp) x)
    (fun x hx => ((hu x (φ.tsupport_subset hx)).contDiffAt
      (ball_isOpen.mem_nhds (φ.tsupport_subset hx))).differentiableAt (by simp))

/-- Equality for actual mathlib distributions, including the derivative sign. -/
theorem distribution_directional_of_smooth {u : ℍ → E} (hu : ContDiffOn ℝ ∞ u Ball) (v : ℍ) :
    Distribution.lineDerivCLM (k := ⊤) v (Distribution.ofFun ballOpen u volume ⊤) =
      Distribution.ofFun ballOpen (fun x => fderiv ℝ u x v) volume ⊤ := by
  ext φ : 1
  rw [Distribution.lineDerivCLM_apply,
    Distribution.ofFun_apply (hu.continuousOn.locallyIntegrableOn ball_isOpen.measurableSet),
    Distribution.ofFun_apply ((contDiffOn_directional hu v).continuousOn.locallyIntegrableOn
      ball_isOpen.measurableSet)]
  exact (integral_test_directional hu v φ).symm

/-- Pointwise local form of the coordinate Laplacian identity. -/
theorem laplacian_eq_sum_directional_at {u : ℍ → E} {a : ℍ} (hu : ContDiffAt ℝ ∞ u a) :
    Laplacian.laplacian u a = ∑ i : Fin 4,
      fderiv ℝ (fun x => fderiv ℝ u x (Fueter.coordinateBasis i)) a
        (Fueter.coordinateBasis i) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis u quaternionONB]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedFDeriv_two_apply]
  rw [fderiv_clm_apply ((hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
    (differentiableAt_const _)]
  simp

theorem contDiffOn_laplacian {u : ℍ → E} (hu : ContDiffOn ℝ ∞ u Ball) :
    ContDiffOn ℝ ∞ (Laplacian.laplacian u) Ball := by
  have hs : ContDiffOn ℝ ∞ (fun a => ∑ i : Fin 4,
      fderiv ℝ (fun x => fderiv ℝ u x (Fueter.coordinateBasis i)) a (Fueter.coordinateBasis i)) Ball :=
    ContDiffOn.sum (fun i _ => contDiffOn_directional (contDiffOn_directional hu _) _)
  apply hs.congr
  intro a ha
  exact laplacian_eq_sum_directional_at ((hu a ha).contDiffAt (ball_isOpen.mem_nhds ha))

/-- Two integrations by parts identify the distributional and classical Laplacians. -/
theorem distributionLaplacian_of_smooth {u : ℍ → E} (hu : ContDiffOn ℝ ∞ u Ball) :
    distributionLaplacian (Distribution.ofFun ballOpen u volume ⊤) =
      Distribution.ofFun ballOpen (Laplacian.laplacian u) volume ⊤ := by
  ext φ : 1
  simp only [distributionLaplacian, FunLike.coe_sum, Finset.sum_apply]
  simp_rw [distribution_directional_of_smooth hu,
    distribution_directional_of_smooth (contDiffOn_directional hu _)]
  have H (i : Fin 4) := (contDiffOn_directional
    (contDiffOn_directional hu (Fueter.coordinateBasis i)) (Fueter.coordinateBasis i)).continuousOn.locallyIntegrableOn
      (μ := volume) ball_isOpen.measurableSet
  simp_rw [Distribution.ofFun_apply (Ω := ballOpen) (H _)]
  rw [Distribution.ofFun_apply ((contDiffOn_laplacian hu).continuousOn.locallyIntegrableOn
    ball_isOpen.measurableSet), ← integral_finsetSum _ (fun i _ => φ.integrable_smul (H i))]
  apply integral_congr_ae
  filter_upwards with a
  by_cases ha : a ∈ Ball
  · rw [laplacian_eq_sum_directional_at ((hu a ha).contDiffAt (ball_isOpen.mem_nhds ha)), Finset.smul_sum]
  · simp [φ.zero_on_compl ha]

variable [CompleteSpace E]

/-- A smooth distributional harmonic function is harmonic in mathlib's sense. -/
theorem harmonicOnNhd_of_smooth_distributionLaplacian_zero {u : ℍ → E}
    (hu : ContDiffOn ℝ ∞ u Ball)
    (hΔ : distributionLaplacian (Distribution.ofFun ballOpen u volume ⊤) = 0) :
    HarmonicOnNhd u Ball := by
  rw [distributionLaplacian_of_smooth hu, ← Distribution.ofFun_zero] at hΔ
  have hcont := (contDiffOn_laplacian hu).continuousOn
  have he := Distribution.ofFun_injective (hcont.locallyIntegrableOn ball_isOpen.measurableSet)
    (locallyIntegrableOn_zero) hΔ
  have hz := Measure.eqOn_open_of_ae_eq he ball_isOpen hcont continuousOn_const
  intro a ha
  refine ⟨((hu a ha).contDiffAt (ball_isOpen.mem_nhds ha)).of_le (by simp), ?_⟩
  filter_upwards [ball_isOpen.mem_nhds ha] with x hx
  exact hz hx

end MathResearch.Spinor
