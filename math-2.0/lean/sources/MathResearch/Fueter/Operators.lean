module

public import Mathlib.Analysis.Quaternion
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Tactic.FinCases

/-!
Real coordinate derivatives and the two constant-coefficient Fueter operators.
The quaternion algebra, normed structure, coordinate basis, Fréchet derivative,
and all smoothness notions are those of mathlib.
-/

@[expose] public section

noncomputable section

open scoped Quaternion Topology BigOperators ContDiff

namespace MathResearch.Fueter

/-- Mathlib's ordered real quaternion basis `(1, i, j, k)`. -/
def coordinateBasis : Module.Basis (Fin 4) ℝ ℍ :=
  QuaternionAlgebra.basisOneIJK (-1) 0 (-1)

/-- The basis has exactly the coordinate order and signs of F-D1. -/
theorem coordinateBasis_eq (μ : Fin 4) :
    coordinateBasis μ = ![(1 : ℍ), ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] μ := by
  apply coordinateBasis.repr.injective
  ext ν
  simp only [Module.Basis.repr_self]
  fin_cases μ <;> fin_cases ν <;> simp [coordinateBasis,
    QuaternionAlgebra.coe_basisOneIJK_repr]

/-- Differentiation in a fixed real direction, expressed with mathlib's Fréchet derivative. -/
def directional (v : ℍ) (f : ℍ → ℍ) (q : ℍ) : ℍ := fderiv ℝ f q v

/-- The ordinary real coordinate partial derivative. Index zero is the real coordinate. -/
def coordPartial (μ : Fin 4) : (ℍ → ℍ) → (ℍ → ℍ) := directional (coordinateBasis μ)

/-- Left multiplication of each coordinate derivative by its basis quaternion. -/
def leftContraction : (ℍ →L[ℝ] ℍ) →L[ℝ] ℍ :=
  ∑ μ : Fin 4, (ContinuousLinearMap.mul ℝ ℍ (coordinateBasis μ)).comp
    (ContinuousLinearMap.apply ℝ ℍ (coordinateBasis μ))

/-- Right multiplication of each coordinate derivative by its basis quaternion. -/
def rightContraction : (ℍ →L[ℝ] ℍ) →L[ℝ] ℍ :=
  ∑ μ : Fin 4, ((ContinuousLinearMap.mul ℝ ℍ).flip (coordinateBasis μ)).comp
    (ContinuousLinearMap.apply ℝ ℍ (coordinateBasis μ))

def leftOperator (f : ℍ → ℍ) (q : ℍ) : ℍ := leftContraction (fderiv ℝ f q)

def rightOperator (f : ℍ → ℍ) (q : ℍ) : ℍ := rightContraction (fderiv ℝ f q)

theorem leftOperator_eq (f : ℍ → ℍ) (q : ℍ) :
    leftOperator f q = ∑ μ : Fin 4, coordinateBasis μ * coordPartial μ f q := by
  simp [leftOperator, leftContraction, coordPartial, directional]

theorem rightOperator_eq (f : ℍ → ℍ) (q : ℍ) :
    rightOperator f q = ∑ μ : Fin 4, coordPartial μ f q * coordinateBasis μ := by
  simp [rightOperator, rightContraction, coordPartial, directional]

/-- Smoothness is included so that the zero-by-convention value of `fderiv` at a
nondifferentiable point cannot witness regularity. -/
def TwoSidedRegularOn (f : ℍ → ℍ) (U : Set ℍ) : Prop :=
  ContDiffOn ℝ ∞ f U ∧
    (∀ q ∈ U, leftOperator f q = 0) ∧ (∀ q ∈ U, rightOperator f q = 0)

theorem contDiffOn_directional {U : Set ℍ} (hU : IsOpen U) {f : ℍ → ℍ}
    (hf : ContDiffOn ℝ ∞ f U) (v : ℍ) : ContDiffOn ℝ ∞ (directional v f) U := by
  exact (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

/-- Evaluation of the derivative of a directional derivative. -/
theorem fderiv_directional {f : ℍ → ℍ} {q : ℍ}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) q) (v w : ℍ) :
    fderiv ℝ (directional v f) q w = fderiv ℝ (fderiv ℝ f) q w v := by
  unfold directional
  rw [fderiv_clm_apply hf (differentiableAt_const v)]
  simp

/-- A constant-coefficient first-order operator commutes with a real directional derivative. -/
theorem contraction_directional {U : Set ℍ} (hU : IsOpen U) {f : ℍ → ℍ}
    (hf : ContDiffOn ℝ ∞ f U) {q : ℍ} (hq : q ∈ U)
    (C : (ℍ →L[ℝ] ℍ) →L[ℝ] ℍ) (v : ℍ) :
    C (fderiv ℝ (directional v f) q) =
      fderiv ℝ (fun x => C (fderiv ℝ f x)) q v := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) q :=
    ((hf.fderiv_of_isOpen (m := ∞) hU (by simp)).contDiffAt (hU.mem_nhds hq)).differentiableAt
      (by simp)
  have hsym := (hf.contDiffAt (hU.mem_nhds hq)).isSymmSndFDerivAt (by simp)
  have heq : fderiv ℝ (directional v f) q = fderiv ℝ (fderiv ℝ f) q v := by
    apply ContinuousLinearMap.ext
    intro w
    rw [fderiv_directional hdf]
    exact hsym.eq w v
  have hc := fderiv_clm_apply (𝕜 := ℝ) (c := fun _ : ℍ => C)
    (u := fderiv ℝ f) (x := q) (differentiableAt_const C) hdf
  rw [heq, hc]
  simp

theorem TwoSidedRegularOn.directional_regular {U : Set ℍ} (hU : IsOpen U) {f : ℍ → ℍ}
    (hf : TwoSidedRegularOn f U) (v : ℍ) : TwoSidedRegularOn (directional v f) U := by
  refine ⟨contDiffOn_directional hU hf.1 v, ?_, ?_⟩
  · intro q hq
    change leftContraction (fderiv ℝ (directional v f) q) = 0
    rw [contraction_directional hU hf.1 hq]
    have hz : (fun x => leftContraction (fderiv ℝ f x)) =ᶠ[𝓝 q] fun _ => (0 : ℍ) :=
      Filter.eventually_of_mem (hU.mem_nhds hq) fun x hx => hf.2.1 x hx
    rw [hz.fderiv_eq, fderiv_fun_const]
    rfl
  · intro q hq
    change rightContraction (fderiv ℝ (directional v f) q) = 0
    rw [contraction_directional hU hf.1 hq]
    have hz : (fun x => rightContraction (fderiv ℝ f x)) =ᶠ[𝓝 q] fun _ => (0 : ℍ) :=
      Filter.eventually_of_mem (hU.mem_nhds hq) fun x hx => hf.2.2 x hx
    rw [hz.fderiv_eq, fderiv_fun_const]
    rfl

/-- Apply a finite ordered list of real coordinate partial derivatives. -/
def iteratedPartial : List (Fin 4) → (ℍ → ℍ) → (ℍ → ℍ)
  | [], f => f
  | μ :: l, f => coordPartial μ (iteratedPartial l f)

theorem TwoSidedRegularOn.iteratedPartial {U : Set ℍ} (hU : IsOpen U) {f : ℍ → ℍ}
    (hf : TwoSidedRegularOn f U) (l : List (Fin 4)) :
    TwoSidedRegularOn (iteratedPartial l f) U := by
  induction l with
  | nil => exact hf
  | cons μ l ih => exact ih.directional_regular hU (coordinateBasis μ)

/-- The multi-index convention `∂₀^α₀ ∂₁^α₁ ∂₂^α₂ ∂₃^α₃`. -/
def multiIndexPartial (α : Fin 4 → ℕ) : (ℍ → ℍ) → (ℍ → ℍ) :=
  iteratedPartial (List.replicate (α 0) 0 ++ List.replicate (α 1) 1 ++
    List.replicate (α 2) 2 ++ List.replicate (α 3) 3)

theorem TwoSidedRegularOn.multiIndexPartial {U : Set ℍ} (hU : IsOpen U) {f : ℍ → ℍ}
    (hf : TwoSidedRegularOn f U) (α : Fin 4 → ℕ) :
    TwoSidedRegularOn (multiIndexPartial α f) U :=
  hf.iteratedPartial hU _

end MathResearch.Fueter
