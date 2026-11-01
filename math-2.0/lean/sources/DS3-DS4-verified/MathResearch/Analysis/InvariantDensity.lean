module
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! Change of variables for an invariant density, using mathlib's measure maps
and nonnegative integrals. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace MathResearch.Analysis
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem map_withDensity_comp (μ : Measure X) {T : X → Y} (hT : Measurable T)
    {w : Y → ℝ≥0∞} (hw : Measurable w) :
    Measure.map T (μ.withDensity (fun x => w (T x))) = (Measure.map T μ).withDensity w := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hT,
    lintegral_withDensity_eq_lintegral_mul _ (show Measurable (fun x => w (T x)) from hw.comp hT)
      (show Measurable (fun x => f (T x)) from hf.comp hT),
    lintegral_withDensity_eq_lintegral_mul _ hw hf,
    lintegral_map (hw.mul hf) hT]
  rfl

theorem measurePreserving_withDensity {μ : Measure X} {T : X → X}
    (hT : MeasurePreserving T μ μ) {w : X → ℝ≥0∞} (hw : Measurable w)
    (hinv : ∀ x, w (T x) = w x) :
    MeasurePreserving T (μ.withDensity w) (μ.withDensity w) := by
  refine ⟨hT.measurable, ?_⟩
  have h := map_withDensity_comp μ hT.measurable hw
  simpa only [hinv, hT.map_eq] using h

end MathResearch.Analysis
