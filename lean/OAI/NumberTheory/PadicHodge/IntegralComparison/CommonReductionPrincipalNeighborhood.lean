import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.PrincipalRefinement

/-! # Common Reduction Principal Neighborhood -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CommonReductionPrincipalNeighborhood

noncomputable section

/-! Refine two actual affine neighborhoods by principal opens with
the same inverse image in a common closed reduction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {Y X₁ X₂ : Scheme.{u}}
  (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
  [IsClosedImmersion f₁] [IsClosedImmersion f₂]
  (U₁ : X₁.Opens) (U₂ : X₂.Opens) (h₁ : IsAffineOpen U₁) (h₂ : IsAffineOpen U₂)
  (y : Y) (hy₁ : f₁ y ∈ U₁) (hy₂ : f₂ y ∈ U₂)

include h₁ h₂ hy₁ hy₂ in
theorem exists_principal : ∃ a₁ : Γ(X₁, U₁), ∃ a₂ : Γ(X₂, U₂),
    f₁ y ∈ X₁.basicOpen a₁ ∧ f₂ y ∈ X₂.basicOpen a₂ ∧
      f₁ ⁻¹ᵁ X₁.basicOpen a₁ = f₂ ⁻¹ᵁ X₂.basicOpen a₂ := by
  obtain ⟨b₁, b₂, he, hy⟩ :=
    exists_basicOpen_le_affine_inter (h₁.preimage f₁) (h₂.preimage f₂) y ⟨hy₁, hy₂⟩
  obtain ⟨a₁, _, ha₁⟩ := Closed.PrincipalRefinement.lift f₁ U₁ h₁ b₁
  obtain ⟨a₂, _, ha₂⟩ := Closed.PrincipalRefinement.lift f₂ U₂ h₂ b₂
  refine ⟨a₁, a₂, ?_, ?_, ha₁.trans (he.trans ha₂.symm)⟩
  · change y ∈ f₁ ⁻¹ᵁ X₁.basicOpen a₁
    rw [ha₁]
    exact hy
  · change y ∈ f₂ ⁻¹ᵁ X₂.basicOpen a₂
    rw [ha₂, ← he]
    exact hy

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CommonReductionPrincipalNeighborhood
