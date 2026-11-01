module
public import MathResearch.Spinor.WeakConstants
public import MathResearch.Spinor.CoefficientEmbedding
public import MathResearch.Spinor.RowAction

/-! The normalized gradient on weighted L² spaces and its complete weak row model.
The row model is the image of the explicitly tested weak polynomial kernel;
identification with the wiki's smooth row realization still requires regularity. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion
open MeasureTheory
namespace MathResearch.Spinor

section L2Transport
variable {X E F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Pointwise transport of a linear isometry equivalence, using mathlib's Lp composition. -/
def l2IsometryEquiv (μ : Measure X) (e : E ≃ₗᵢ[ℂ] F) : Lp E 2 μ ≃ₗᵢ[ℂ] Lp F 2 μ where
  toLinearMap := e.toContinuousLinearEquiv.toContinuousLinearMap.compLpₗ 2 μ
  invFun := e.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLp
  left_inv f := by
    apply Lp.ext
    filter_upwards [e.symm.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp
      (e.toContinuousLinearEquiv.toContinuousLinearMap.compLp f),
      e.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp f] with q h₁ h₂
    change (e.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLp
      (e.toContinuousLinearEquiv.toContinuousLinearMap.compLp f)) q = f q
    rw [h₁, h₂]
    exact e.symm_apply_apply (f q)
  right_inv f := by
    apply Lp.ext
    filter_upwards [e.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp
      (e.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLp f),
      e.symm.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp f] with q h₁ h₂
    change (e.toContinuousLinearEquiv.toContinuousLinearMap.compLp
      (e.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLp f)) q = f q
    rw [h₁, h₂]
    exact e.apply_symm_apply (f q)
  norm_map' f := by
    change ‖e.toContinuousLinearEquiv.toContinuousLinearMap.compLp f‖ = ‖f‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [l2_norm_sq_integral, l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [e.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp f] with q hq
    rw [hq]
    exact congrArg (fun r : ℝ => r^2) (e.norm_map (f q))

theorem l2IsometryEquiv_ae (μ : Measure X) (e : E ≃ₗᵢ[ℂ] F) (f : Lp E 2 μ) :
    (l2IsometryEquiv μ e f : X → F) =ᵐ[μ] fun x => e (f x) :=
  e.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp f
end L2Transport

abbrev CompatibleBallL2 (m : ℕ) := Lp (CompatibleRow m) 2 (weightedBallMeasure (m+1))

/-- DS1's actual fibre map, extended pointwise to weighted L² equivalence classes. -/
def spinorL2Isometry (m : ℕ) : BallL2 (m+1) ≃ₗᵢ[ℂ] CompatibleBallL2 m :=
  l2IsometryEquiv (weightedBallMeasure (m+1)) (spinorIsometry m)

/-- The weak compatible-row kernel, as the image under the explicitly normalized gradient. -/
def weakRowKernel (m : ℕ) (hm : 1 ≤ m) : Submodule ℂ (CompatibleBallL2 m) :=
  (weakKernel (m+1) (by omega)).map (spinorL2Isometry m).toLinearEquiv.toLinearMap

/-- The complete weak-model isometry; it does not assert smooth representatives exist. -/
def weakSpinorIsometry (m : ℕ) (hm : 1 ≤ m) :
    WeakBallSpace (m+1) (by omega) ≃ₗᵢ[ℂ] weakRowKernel m hm :=
  (spinorL2Isometry m).submoduleMap (weakKernel (m+1) (by omega))

instance weakRowKernel_completeSpace (m : ℕ) (hm : 1 ≤ m) : CompleteSpace (weakRowKernel m hm) :=
  (weakSpinorIsometry m hm).toIsometryEquiv.completeSpace_iff.mp inferInstance

instance weakRowKernel_nontrivial (m : ℕ) (hm : 1 ≤ m) : Nontrivial (weakRowKernel m hm) :=
  (weakSpinorIsometry m hm).injective.nontrivial

/-- A compact unconditional portion of DS2: both explicitly defined weak models are
nonzero complete complex Hilbert spaces, with the normalized pointwise L² isometry. -/
theorem DS2_weak_models (m : ℕ) (hm : 1 ≤ m) :
    CompleteSpace (WeakBallSpace (m+1) (by omega)) ∧ Nontrivial (WeakBallSpace (m+1) (by omega)) ∧
    CompleteSpace (weakRowKernel m hm) ∧ Nontrivial (weakRowKernel m hm) ∧
    Nonempty (WeakBallSpace (m+1) (by omega) ≃ₗᵢ[ℂ] weakRowKernel m hm) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, ⟨weakSpinorIsometry m hm⟩⟩

end MathResearch.Spinor
