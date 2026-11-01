module
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! The Hilbert-space argument in DS3, with its analytic and finite-dimensional
inputs explicit. Irreducible here means closed invariant subspaces, not algebraic simplicity. -/
@[expose] public section
noncomputable section
open MeasureTheory
namespace MathResearch.Spinor

variable {G H V K : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [MeasurableSpace K]

/-- Invariance for the actual unitary group action. -/
def UnitaryInvariant (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (M : Submodule ℂ H) : Prop :=
  ∀ g x, x ∈ M → ρ g x ∈ M

/-- Hilbert/topological irreducibility; no assertion about nonclosed subspaces. -/
def TopologicallyIrreducible (ρ : G →* (H ≃ₗᵢ[ℂ] H)) : Prop :=
  ∀ M : Submodule ℂ H, IsClosed (M : Set H) → UnitaryInvariant ρ M → M = ⊥ ∨ M = ⊤

omit [CompleteSpace H] in
theorem UnitaryInvariant.orthogonal {ρ : G →* (H ≃ₗᵢ[ℂ] H)} {M : Submodule ℂ H}
    (hM : UnitaryInvariant ρ M) : UnitaryInvariant ρ Mᗮ := by
  intro g x hx
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro y hy
  have hi : ρ g (ρ g⁻¹ y) = y := by simp
  rw [← hi, (ρ g).inner_map_map]
  exact hx _ (hM g⁻¹ y hy)

/-- Averaging stays in any closed invariant subspace, by mathlib's Bochner-integral theorem. -/
theorem compact_average_mem (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (μ : Measure K)
    [IsProbabilityMeasure μ] (kL : K → G) (M : Submodule ℂ H)
    (hclosed : IsClosed (M : Set H)) (hinv : UnitaryInvariant ρ M) (f : H) (hf : f ∈ M)
    (hint : Integrable (fun k => ρ (kL k) f) μ) :
    (∫ k, ρ (kL k) f ∂μ) ∈ M :=
  (M.restrictScalars ℝ).convex.integral_mem hclosed (Filter.Eventually.of_forall fun _ => hinv _ _ hf) hint

/-- Explicit hypotheses supplied, in DS3, by harmonic mean values, point evaluation,
transitivity, and irreducibility of the compact polynomial representation. -/
structure CompactAveragingInputs (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (μ : Measure K)
    (kL : K → G) (c : V →ₗᵢ[ℂ] H) (ev0 : H →L[ℂ] V) : Prop where
  average_integrable : ∀ f : H, Integrable (fun k => ρ (kL k) f) μ
  average_eq_constant : ∀ f : H, (∫ k, ρ (kL k) f ∂μ) = c (ev0 f)
  translate_detects : ∀ f : H, f ≠ 0 → ∃ g : G, ev0 (ρ g f) ≠ 0
  constant_orbit_spans : ∀ v : V, v ≠ 0 →
    LinearMap.range c.toLinearMap ≤ Submodule.span ℂ (Set.range fun g : G => ρ g (c v))

theorem constants_le_of_nonzero_invariant (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (μ : Measure K)
    [IsProbabilityMeasure μ] (kL : K → G) (c : V →ₗᵢ[ℂ] H) (ev0 : H →L[ℂ] V)
    (h : CompactAveragingInputs ρ μ kL c ev0)
    (M : Submodule ℂ H) (hclosed : IsClosed (M : Set H)) (hinv : UnitaryInvariant ρ M)
    (hne : M ≠ ⊥) : LinearMap.range c.toLinearMap ≤ M := by
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨g, hg⟩ := h.translate_detects f hf0
  have hc : c (ev0 (ρ g f)) ∈ M := by
    rw [← h.average_eq_constant]
    exact compact_average_mem ρ μ kL M hclosed hinv _ (hinv g f hf) (h.average_integrable _)
  apply (h.constant_orbit_spans _ hg).trans
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  exact hinv a _ hc

/-- DS3's orthogonal-complement argument, conditional on the four displayed inputs. -/
theorem DS3_irreducible_of_compactAveraging [Nontrivial V]
    (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (μ : Measure K) [IsProbabilityMeasure μ]
    (kL : K → G) (c : V →ₗᵢ[ℂ] H) (ev0 : H →L[ℂ] V)
    (h : CompactAveragingInputs ρ μ kL c ev0) : TopologicallyIrreducible ρ := by
  intro M hclosed hinv
  by_cases hM : M = ⊥
  · exact Or.inl hM
  right
  let : CompleteSpace M := hclosed.completeSpace_coe
  apply Submodule.orthogonal_eq_bot_iff.mp
  by_contra hperp
  have h₁ := constants_le_of_nonzero_invariant ρ μ kL c ev0 h M hclosed hinv hM
  have h₂ := constants_le_of_nonzero_invariant ρ μ kL c ev0 h Mᗮ
    M.isClosed_orthogonal hinv.orthogonal hperp
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hr : c v ∈ LinearMap.range c.toLinearMap := ⟨v, rfl⟩
  have hz : c v = 0 := inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal (h₁ hr) (h₂ hr))
  exact hv (c.injective (hz.trans c.map_zero.symm))

/-- The algebraic span of all translates of a subspace. -/
def translateSpan (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (C : Submodule ℂ H) : Submodule ℂ H :=
  Submodule.span ℂ {x | ∃ g v, v ∈ C ∧ x = ρ g v}

omit [CompleteSpace H] in
theorem translateSpan_invariant (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (C : Submodule ℂ H) :
    UnitaryInvariant ρ (translateSpan ρ C) := by
  intro g x hx
  change x ∈ (translateSpan ρ C).comap (ρ g).toLinearEquiv.toLinearMap
  apply Submodule.span_le.mpr _ hx
  rintro y ⟨a, v, hv, rfl⟩
  change ρ g (ρ a v) ∈ translateSpan ρ C
  apply Submodule.subset_span
  exact ⟨g*a, v, hv, by simp [map_mul]⟩

omit [CompleteSpace H] in
theorem UnitaryInvariant.topologicalClosure {ρ : G →* (H ≃ₗᵢ[ℂ] H)} {M : Submodule ℂ H}
    (hM : UnitaryInvariant ρ M) : UnitaryInvariant ρ M.topologicalClosure := by
  intro g x hx
  have hle : M ≤ M.topologicalClosure.comap (ρ g).toLinearEquiv.toLinearMap :=
    fun y hy => M.le_topologicalClosure (hM g y hy)
  exact M.topologicalClosure_minimal hle
    (M.isClosed_topologicalClosure.preimage (ρ g).continuous) hx

omit [CompleteSpace H] in
/-- The second conclusion of DS3 follows for every nonzero constant subspace. -/
theorem DS3_dense_translateSpan {ρ : G →* (H ≃ₗᵢ[ℂ] H)}
    (hirred : TopologicallyIrreducible ρ) (C : Submodule ℂ H) (hC : C ≠ ⊥) :
    (translateSpan ρ C).topologicalClosure = ⊤ := by
  have hd := hirred _ (translateSpan ρ C).isClosed_topologicalClosure
    (translateSpan_invariant ρ C).topologicalClosure
  rcases hd with hd | hd
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hC
    have hm : v ∈ translateSpan ρ C := Submodule.subset_span ⟨1, v, hv, by simp⟩
    have := (translateSpan ρ C).le_topologicalClosure hm
    rw [hd, Submodule.mem_bot] at this
    exact False.elim (hv0 this)
  · exact hd

end MathResearch.Spinor
