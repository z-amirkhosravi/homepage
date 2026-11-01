module
public import MathResearch.Spinor.SchmidCovariance
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Intrinsic group derivatives and left-translation invariance of the verified kernel. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion BigOperators Matrix.Norms.Elementwise Topology
namespace MathResearch.Spinor

def matrixLeftCLM (g : QuaternionMatrix2) : QuaternionMatrix2 →L[ℝ] QuaternionMatrix2 :=
  (LinearMap.mulLeft ℝ g).toContinuousLinearMap

@[simp] theorem matrixLeftCLM_apply (g h : QuaternionMatrix2) : matrixLeftCLM g h = g*h := rfl

theorem differentiableAt_ballSection (q : ℍ) (hq : q ∈ Ball) : DifferentiableAt ℝ ballSection q := by
  have hr := ((hasFDerivAt_inv ((Real.sqrt_pos.mpr hq).ne')).comp q
    ((hasFDerivAt_ballScale q).sqrt (ne_of_gt hq))).differentiableAt
  have hb : DifferentiableAt ℝ (fun x : ℍ => (1 : QuaternionMatrix2) + tangentCLM x) q :=
    (differentiableAt_const _).add tangentCLM.differentiableAt
  convert! hr.smul hb using 1
  funext x
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;> simp [ballSection, tangentMatrix]

@[simp] theorem ballSection_zero : ballSection 0 = 1 := by
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;> simp [ballSection, ballScale]

/-- A curve lying in G near zero with tangent gξ_v; no ambient extension affects this derivative. -/
def rightSectionPath (g : QuaternionMatrix2) (v : ℍ) (t : ℝ) : QuaternionMatrix2 :=
  g * ballSection (t • v)

@[simp] theorem rightSectionPath_zero (g : QuaternionMatrix2) (v : ℍ) : rightSectionPath g v 0 = g := by
  simp [rightSectionPath]

theorem rightSectionPath_hasDerivAt (g : QuaternionMatrix2) (v : ℍ) :
    HasDerivAt (rightSectionPath g v) (g*tangentMatrix v) 0 := by
  have h0 : (0 : ℍ) ∈ Ball := by simp [Ball, ballScale]
  have hσ : HasFDerivAt ballSection (fderiv ℝ ballSection 0) ((fun t : ℝ => t • v) 0) := by
    simpa using (differentiableAt_ballSection 0 h0).hasFDerivAt
  have hd := (matrixLeftCLM g).hasFDerivAt.comp_hasDerivAt 0
    (hσ.comp_hasDerivAt 0 ((hasDerivAt_id (0:ℝ)).smul_const v))
  simpa [rightSectionPath, Function.comp_def, fderiv_ballSection 0 v h0, ballScale] using! hd

/-- Agreement on G implies agreement of its tangent derivatives, for differentiable representatives. -/
theorem rightLieDerivative_congr_on_group (n : ℕ) (F H : QuaternionMatrix2 → BinaryForm n)
    (he : ∀ g, IsSp11 g → F g = H g) {g : QuaternionMatrix2} (hg : IsSp11 g)
    (hF : DifferentiableAt ℝ F g) (hH : DifferentiableAt ℝ H g) (v : ℍ) :
    rightLieDerivative n F g v = rightLieDerivative n H g v := by
  have h0 : (0 : ℍ) ∈ Ball := by simp [Ball, ballScale]
  have hc : ContinuousAt (fun t : ℝ => t • v) 0 := ((hasDerivAt_id (0:ℝ)).smul_const v).continuousAt
  have ht : ∀ᶠ t : ℝ in 𝓝 0, t • v ∈ Ball :=
    hc.eventually (by simpa using ball_isOpen.mem_nhds h0)
  have hEq : (fun t => F (rightSectionPath g v t)) =ᶠ[𝓝 0] fun t => H (rightSectionPath g v t) :=
    ht.mono fun t h => he _ (hg.mul (ballSection_isSp11 _ h))
  rw [← rightLieDerivative_eq_path n F g hF v (rightSectionPath g v) (rightSectionPath_zero g v) (rightSectionPath_hasDerivAt g v),
    ← rightLieDerivative_eq_path n H g hH v (rightSectionPath g v) (rightSectionPath_zero g v) (rightSectionPath_hasDerivAt g v)]
  exact hEq.deriv_eq

open scoped Matrix.Norms.Operator in
/-- The right derivative also equals the wiki's derivative along the actual matrix exponential. -/
theorem rightLieDerivative_eq_exp (n : ℕ) (F : QuaternionMatrix2 → BinaryForm n)
    (g : QuaternionMatrix2) (hF : DifferentiableAt ℝ F g) (v : ℍ) :
    deriv (fun t : ℝ => F (g * NormedSpace.exp (t • tangentMatrix v))) 0 =
      rightLieDerivative n F g v := by
  apply rightLieDerivative_eq_path n F g hF v
  · simp
  · simpa using (hasDerivAt_exp_smul_const (tangentMatrix v) (0 : ℝ)).const_mul g

/-- Projected operators are independent of the differentiable extension off G. -/
theorem projectedGroupOperator_congr_on_group (n : ℕ) (F H : QuaternionMatrix2 → BinaryForm n)
    (he : ∀ g, IsSp11 g → F g = H g) {g : QuaternionMatrix2} (hg : IsSp11 g)
    (hF : DifferentiableAt ℝ F g) (hH : DifferentiableAt ℝ H g) (d : Fin 2 →₀ ℕ) :
    projectedGroupOperator n F g d = projectedGroupOperator n H g d := by
  simp only [projectedGroupOperator, rightLieDerivative_congr_on_group n F H he hg hF hH]

/-- The moving-frame formula for every differentiable right-equivariant representative. -/
theorem SC1_equivariant_frame_v1 (m : ℕ) (F : QuaternionMatrix2 → BinaryForm (m+1))
    (hK : RightEquivariant (m+1) F) (hF : ∀ g, IsSp11 g → DifferentiableAt ℝ F g)
    (q v : ℍ) (hq : q ∈ Ball) :
    rightLieDerivative (m+1) F (ballSection q) v =
      ballScale q • fderiv ℝ (fun x => F (ballSection x)) q v +
        infinitesimalAction m (quaternionMatrix (connectionCoefficient q v)) (F (ballSection q)) := by
  let U := fun x => F (ballSection x)
  have hU : ∀ x ∈ Ball, DifferentiableAt ℝ U x := fun x hx =>
    (hF _ (ballSection_isSp11 x hx)).comp x (differentiableAt_ballSection x hx)
  have hlift : DifferentiableAt ℝ (frameLift (m+1) U) (ballSection q) :=
    differentiableAt_frameLift (m+1) U (ballSection_isSp11 q hq)
      (by simpa [groupOrigin_ballSection q hq] using hU q hq)
  rw [← rightLieDerivative_congr_on_group (m+1) (frameLift (m+1) U) F
    (fun g hg => frameLift_recover (m+1) F hK hg) (ballSection_isSp11 q hq) hlift (hF _ (ballSection_isSp11 q hq)) v]
  exact SC1_frame_v1 m U q v hq (hU q hq)

/-- Left translation commutes with the projected right derivative. -/
theorem projectedGroupOperator_left_translate (n : ℕ) (F : QuaternionMatrix2 → BinaryForm n)
    (a g : QuaternionMatrix2) (d : Fin 2 →₀ ℕ) :
    projectedGroupOperator n (fun x => F (a*x)) g d = projectedGroupOperator n F (a*g) d := by
  have he (v : ℍ) : (fun t => F (a * rightAffinePath g v t)) =
      (fun t => F (rightAffinePath (a*g) v t)) := by
    funext t
    simp [rightAffinePath, mul_add, mul_assoc]
  simp only [projectedGroupOperator, rightLieDerivative, he]

/-- SC1/v1 for an arbitrary differentiable right-equivariant group representative. -/
theorem SC1_v1 (m : ℕ) (F : QuaternionMatrix2 → BinaryForm (m+1))
    (hK : RightEquivariant (m+1) F) (hF : ∀ g, IsSp11 g → DifferentiableAt ℝ F g)
    (q : ℍ) (hq : q ∈ Ball) :
    (∀ v, ballSectionInverse q * fderiv ℝ ballSection q v =
      (ballScale q)⁻¹ • !![(2:ℝ)⁻¹ • (v * star q - q * star v), v;
        star v, connectionCoefficient q v]) ∧
    (∀ v w, ballCurvature q v w = -(ballScale q)⁻¹ ^ 2 • (star v * w - star w * v)) ∧
    (∀ v, rightLieDerivative (m+1) F (ballSection q) v =
      ballScale q • fderiv ℝ (fun x => F (ballSection x)) q v +
        infinitesimalAction m (quaternionMatrix (connectionCoefficient q v)) (F (ballSection q))) :=
  ⟨fun v => ballSection_maurerCartan q v hq, fun v w => ballCurvature_eq q v w hq,
    fun v => SC1_equivariant_frame_v1 m F hK hF q v hq⟩

end MathResearch.Spinor
