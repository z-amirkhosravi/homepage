module
public import MathResearch.Spinor.ClassicalRow
public import MathResearch.Spinor.CompactContinuity

/-! The complete compatible-row action, transferred by the normalized gradient
and identified with the independently written C3 formula on L² representatives. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Quaternion
open MeasureTheory
namespace MathResearch.Spinor

theorem quaternionCoefficients_spinorIsometry (m : ℕ) (p : BinaryForm (m+1)) (k : Fin (m+1)) :
    quaternionCoefficients m (spinorIsometry m p).val k = normalizedFueterRow m p k := by
  exact rowCoefficient_spinorIsometry m (exponent m k) p

def regularRowUnitary (m : ℕ) (hm : 1 ≤ m) (g : Sp11) :
    weakRowKernel m hm ≃ₗᵢ[ℂ] weakRowKernel m hm :=
  ((weakSpinorIsometry m hm).symm.trans (regularRepresentation (m+1) (by omega) g)).trans
    (weakSpinorIsometry m hm)

def regularRowRepresentation (m : ℕ) (hm : 1 ≤ m) :
    Sp11 →* (weakRowKernel m hm ≃ₗᵢ[ℂ] weakRowKernel m hm) where
  toFun := regularRowUnitary m hm
  map_one' := by
    ext h : 1
    simp [regularRowUnitary]
  map_mul' g k := by
    ext h : 1
    simp [regularRowUnitary, map_mul]

/-- The normalized L² isometry intertwines the actual two group representations. -/
theorem regularRow_intertwining (m : ℕ) (hm : 1 ≤ m) (g : Sp11)
    (f : WeakBallSpace (m+1) (by omega)) :
    regularRowRepresentation m hm g (weakSpinorIsometry m hm f) =
      weakSpinorIsometry m hm (regularRepresentation (m+1) (by omega) g f) := by
  change weakSpinorIsometry m hm (regularRepresentation (m+1) (by omega) g
    ((weakSpinorIsometry m hm).symm (weakSpinorIsometry m hm f))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem stronglyContinuous_regularRowRepresentation (m : ℕ) (hm : 1 ≤ m)
    (h : weakRowKernel m hm) : Continuous (fun g : Sp11 => regularRowRepresentation m hm g h) :=
  (weakSpinorIsometry m hm).continuous.comp
    (stronglyContinuous_regularRepresentation_by_compact (m+1) (by omega) ((weakSpinorIsometry m hm).symm h))

theorem weakSpinorIsometry_ae (m : ℕ) (hm : 1 ≤ m)
    (f : WeakBallSpace (m+1) (by omega)) :
    ((weakSpinorIsometry m hm f).val : ℍ → CompatibleRow m) =ᵐ[weightedBallMeasure (m+1)]
      fun q => spinorIsometry m (f.val q) :=
  l2IsometryEquiv_ae (weightedBallMeasure (m+1)) (spinorIsometry m) f.val

/-- The transported row action is exactly C3, including inverse, transpose,
and right multiplication by complex coefficients, almost everywhere. -/
theorem regularRowRepresentation_ae (m : ℕ) (hm : 1 ≤ m) (g : Sp11)
    (h : weakRowKernel m hm) :
    ∀ᵐ q ∂weightedBallMeasure (m+1), ∀ k,
      quaternionCoefficients m (((regularRowRepresentation m hm g h).val q).val) k =
        rowBallRepresentation m g (fun x => quaternionCoefficients m ((h.val x).val)) q k := by
  let f := (weakSpinorIsometry m hm).symm h
  have hin := weakSpinorIsometry_ae m hm f
  rw [show weakSpinorIsometry m hm f = h from (weakSpinorIsometry m hm).apply_symm_apply h] at hin
  have hpull := (mobius_quasiMeasurePreserving_weighted (m+1) (by omega)
    (isSp11_signatureAdjoint g.property)).ae hin
  have hout := weakSpinorIsometry_ae m hm (regularRepresentation (m+1) (by omega) g f)
  have haction := weightedL2Action_ae (m+1) (by omega) g f.val
  have he : regularRowRepresentation m hm g h =
      weakSpinorIsometry m hm (regularRepresentation (m+1) (by omega) g f) := rfl
  rw [he]
  filter_upwards [hout, haction, hpull] with q hq hact hpre
  intro k
  rw [hq]
  change quaternionCoefficients m (spinorIsometry m (weightedL2Action (m+1) (by omega) g f.val q)).val k = _
  rw [hact, quaternionCoefficients_spinorIsometry, DS2_row_intertwining]
  simp only [rowBallRepresentation, rowBallAction, hpre]
  rw [show quaternionCoefficients m (spinorIsometry m (f.val (mobiusPoint (signatureAdjoint g) q))).val =
    normalizedFueterRow m (f.val (mobiusPoint (signatureAdjoint g) q)) from
      funext (quaternionCoefficients_spinorIsometry m _)]

end MathResearch.Spinor
