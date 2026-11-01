module
public import MathResearch.Spinor.CompactAveraging

/-! Elementary invariant-subspace and transport lemmas. The research proofs
call these results; their abstract linear-algebra proofs are kept separate. -/
@[expose] public section
noncomputable section
namespace MathResearch.Spinor

/-- The elementary invariant-span step, with the ambient Hilbert space abstract.
This merely packages the application of irreducibility to the constants. -/
theorem equivariant_irreducible_range_le_span
    {G K H V : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (c : V →ₗᵢ[ℂ] H)
    (σ : K → V →ₗ[ℂ] V) (ι : K → G)
    (he : ∀ k v, c (σ k v) = ρ (ι k) (c v))
    (hir : ∀ M : Submodule ℂ V, (∀ k v, v ∈ M → σ k v ∈ M) → M = ⊥ ∨ M = ⊤)
    (v : V) (hv : v ≠ 0) :
    LinearMap.range c.toLinearMap ≤ Submodule.span ℂ (Set.range fun g : G => ρ g (c v)) := by
  let S := Submodule.span ℂ (Set.range fun g : G => ρ g (c v))
  have hs : UnitaryInvariant ρ S := by
    intro g x hx
    change x ∈ S.comap (ρ g).toLinearEquiv.toLinearMap
    apply Submodule.span_le.mpr _ hx
    rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span ⟨g*a, by simp [map_mul]⟩
  let M := S.comap c.toLinearMap
  have hM : ∀ k p, p ∈ M → σ k p ∈ M := by
    intro k p hp
    change c (σ k p) ∈ S
    rw [he]
    exact hs _ _ hp
  have hvM : v ∈ M := by
    change c v ∈ S
    apply Submodule.subset_span
    exact ⟨1, by simp⟩
  have hne : M ≠ ⊥ := by
    intro hz
    rw [hz, Submodule.mem_bot] at hvM
    exact hv hvM
  have ht := (hir M hM).resolve_left hne
  rintro x ⟨p, rfl⟩
  exact (show p ∈ M from ht ▸ Submodule.mem_top)

/-- Transport of topological irreducibility through an intertwining unitary equivalence. -/
theorem TopologicallyIrreducible.transport
    {G H H' : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (σ : G →* (H' ≃ₗᵢ[ℂ] H')) (e : H ≃ₗᵢ[ℂ] H')
    (he : ∀ g x, σ g (e x) = e (ρ g x)) (hi : TopologicallyIrreducible ρ) :
    TopologicallyIrreducible σ := by
  intro M hc hm
  have hMc : IsClosed ((M.comap e.toLinearEquiv.toLinearMap : Submodule ℂ H) : Set H) :=
    hc.preimage e.continuous
  have hMi : UnitaryInvariant ρ (M.comap e.toLinearEquiv.toLinearMap) := by
    intro g x hx
    change e (ρ g x) ∈ M
    rw [← he]
    exact hm g _ hx
  rcases hi _ hMc hMi with h | h
  · left
    apply le_antisymm _ bot_le
    intro y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    have hx : x ∈ M.comap e.toLinearEquiv.toLinearMap := hy
    rw [h, Submodule.mem_bot] at hx
    simp [hx]
  · right
    apply le_antisymm le_top
    intro y _
    obtain ⟨x, rfl⟩ := e.surjective y
    exact (show x ∈ M.comap e.toLinearEquiv.toLinearMap from h ▸ Submodule.mem_top)


/-- Transfer an intertwining isometry to a unitarily equivalent model. -/
theorem intertwiningIsometry_transport
    {G H H' L : Type*} [Group G] [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup H'] [NormedSpace ℂ H'] [NormedAddCommGroup L] [NormedSpace ℂ L]
    (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (σ : G →* (H' ≃ₗᵢ[ℂ] H')) (τ : G →* (L ≃ₗᵢ[ℂ] L))
    (e : H ≃ₗᵢ[ℂ] H') (E : H →ₗᵢ[ℂ] L)
    (he : ∀ a x, σ a (e x) = e (ρ a x))
    (hE : ∀ a x, E (ρ a x) = τ a (E x)) (a : G) (y : H') :
    (E.comp e.symm.toLinearIsometry) (σ a y) = τ a ((E.comp e.symm.toLinearIsometry) y) := by
  change E (e.symm (σ a y)) = τ a (E (e.symm y))
  have h : e.symm (σ a y) = ρ a (e.symm y) := by
    apply e.injective
    rw [e.apply_symm_apply, ← he, e.apply_symm_apply]
  rw [h, hE]

end MathResearch.Spinor
