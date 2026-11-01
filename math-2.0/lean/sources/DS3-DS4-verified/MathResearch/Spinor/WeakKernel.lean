module
public import MathResearch.Spinor.WeightedMeasure
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The weak Fueter kernel as a closed subspace of the actual weighted L² space.
The defining tests use the adjoint of the coefficient symbol of D_l T_n.
This file does not assert Weyl regularity or the classical/weak comparison. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion BigOperators Distributions
open MeasureTheory
namespace MathResearch.Spinor

def ballOpen : TopologicalSpace.Opens ℍ := ⟨Ball, ball_isOpen⟩
abbrev BallTest := 𝓓(ballOpen, ℝ)

/-- The `(j,d)` coefficient of the symbol e_μ T_n, complex linear in the spinor. -/
def weakSymbol (n : ℕ) (μ : Fin 4) (j : Fin 2) (d : Fin 2 →₀ ℕ) :
    BinaryForm n →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (spinorProjection n (Fueter.coordinateBasis μ) p j).coeff d
      map_add' := by
        intro p r
        rw [spinorProjection_add_right]
        simp
      map_smul' := by
        intro c p
        simp [spinorProjection, matrixColumn]
        ring }

/-- Formal-adjoint test vector; inverse density converts the weighted pairing to Lebesgue testing. -/
def weakTestVector (n : ℕ) (φ : BallTest) (j : Fin 2) (d : Fin 2 →₀ ℕ) (q : ℍ) : BinaryForm n :=
  (ballDensity n q)⁻¹ • ∑ μ : Fin 4,
    (fderiv ℝ φ q (Fueter.coordinateBasis μ)) • (weakSymbol n μ j d).adjoint 1

theorem weakTestVector_tsupport (n : ℕ) (φ : BallTest) (j : Fin 2) (d : Fin 2 →₀ ℕ) :
    tsupport (weakTestVector n φ j d) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro q hq
  by_contra h
  have hz (μ : Fin 4) : fderiv ℝ φ q (Fueter.coordinateBasis μ) = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun x => fderiv ℝ φ x (Fueter.coordinateBasis μ))
      (fun hx => h ((tsupport_fderiv_apply_subset ℝ _ ) hx))
  exact hq (by simp [weakTestVector, hz])

theorem weakTestVector_continuous (n : ℕ) (hn : 2 ≤ n) (φ : BallTest)
    (j : Fin 2) (d : Fin 2 →₀ ℕ) : Continuous (weakTestVector n φ j d) := by
  apply ContinuousOn.continuous_of_tsupport_subset _ ball_isOpen
    ((weakTestVector_tsupport n φ j d).trans φ.tsupport_subset)
  unfold weakTestVector
  have hw := (continuous_ballDensity n).continuousOn.inv₀ (s := Ball)
    (fun q hq => (ballDensity_pos n hn hq).ne')
  apply hw.smul
  · apply Continuous.continuousOn
    apply continuous_finsetSum
    intro μ _
    exact ((φ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const).smul continuous_const

instance weightedBallMeasure_locallyFinite (n : ℕ) : IsLocallyFiniteMeasure (weightedBallMeasure n) :=
  IsLocallyFiniteMeasure.withDensity_ofReal (continuous_ballDensity n)

theorem weakTestVector_memLp (n : ℕ) (hn : 2 ≤ n) (φ : BallTest)
    (j : Fin 2) (d : Fin 2 →₀ ℕ) : MemLp (weakTestVector n φ j d) 2 (weightedBallMeasure n) :=
  (weakTestVector_continuous n hn φ j d).memLp_of_hasCompactSupport
    (φ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) (weakTestVector_tsupport n φ j d))

/-- The continuous complex-linear weak differential test. -/
def weakTest (n : ℕ) (hn : 2 ≤ n) (φ : BallTest) (j : Fin 2) (d : Fin 2 →₀ ℕ) :
    BallL2 n →L[ℂ] ℂ :=
  innerSL ℂ ((weakTestVector_memLp n hn φ j d).toLp (weakTestVector n φ j d))

/-- All real compactly supported smooth tests and all polynomial coefficients are imposed. -/
def weakKernel (n : ℕ) (hn : 2 ≤ n) : Submodule ℂ (BallL2 n) :=
  ⨅ (φ : BallTest) (j : Fin 2) (d : Fin 2 →₀ ℕ), (weakTest n hn φ j d).ker

@[simp] theorem mem_weakKernel (n : ℕ) (hn : 2 ≤ n) (f : BallL2 n) :
    f ∈ weakKernel n hn ↔ ∀ φ j d, weakTest n hn φ j d f = 0 := by
  simp [weakKernel]

theorem weakKernel_isClosed (n : ℕ) (hn : 2 ≤ n) : IsClosed (weakKernel n hn : Set (BallL2 n)) := by
  simp only [weakKernel, Submodule.coe_iInf]
  exact isClosed_iInter fun φ => isClosed_iInter fun j => isClosed_iInter fun d =>
    (weakTest n hn φ j d).isClosed_ker

instance weakKernel_completeSpace (n : ℕ) (hn : 2 ≤ n) : CompleteSpace (weakKernel n hn) :=
  (weakKernel_isClosed n hn).completeSpace_coe

/-- The Hilbert space of weak polynomial spinors. No regularity hypothesis is used for completeness. -/
abbrev WeakBallSpace (n : ℕ) (hn : 2 ≤ n) := weakKernel n hn

/-- The test vector really is the formal-adjoint symbol against Lebesgue measure:
its weighted inner product is the sum of directional derivatives of the test times the symbol. -/
theorem weakTestVector_pairing (n : ℕ) (hn : 2 ≤ n) (φ : BallTest)
    (j : Fin 2) (d : Fin 2 →₀ ℕ) (p : BinaryForm n) {q : ℍ} (hq : q ∈ Ball) :
    (ballDensity n q : ℂ) * inner ℂ (weakTestVector n φ j d q) p =
      ∑ μ : Fin 4, (fderiv ℝ φ q (Fueter.coordinateBasis μ) : ℂ) * weakSymbol n μ j d p := by
  have hr (r : ℝ) (v : BinaryForm n) : inner ℂ (r • v) p = (r : ℂ) * inner ℂ v p := by
    change inner ℂ ((r:ℂ) • v) p = _
    rw [inner_smul_left]
    simp
  simp only [weakTestVector, hr, sum_inner, ContinuousLinearMap.adjoint_inner_left,
    RCLike.inner_apply, map_one, mul_one]
  rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (ballDensity_pos n hn hq).ne']
  simp

end MathResearch.Spinor
