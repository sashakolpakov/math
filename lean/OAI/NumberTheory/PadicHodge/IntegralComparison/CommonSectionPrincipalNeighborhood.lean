import OAI.NumberTheory.PadicHodge.IntegralComparison.CommonReductionPrincipalNeighborhood

/-! # Common Section Principal Neighborhood -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CommonSectionPrincipalNeighborhood

noncomputable section

/-! Common principal neighborhoods retain the whole sections when
their reduced base has one point and surjects onto the original base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {T₀ T Y X₁ X₂ : Scheme.{u}}
  [Subsingleton T₀] [Nonempty T₀]
  (r : T₀ ⟶ T) (hr : Function.Surjective r)
  (s₀ : T₀ ⟶ Y)

include hr in
omit [Nonempty ↥T₀] in
theorem contains {X : Scheme.{u}} (f : Y ⟶ X) (s : T ⟶ X)
    (h : s₀ ≫ f = r ≫ s) (U : X.Opens) (z : T₀) (hz : f (s₀ z) ∈ U) :
    ⊤ ≤ s ⁻¹ᵁ U := by
  intro t _
  obtain ⟨z', rfl⟩ := hr t
  have he : z' = z := Subsingleton.elim _ _
  subst z'
  have hw : f (s₀ z) = s (r z) := congrArg (fun g : T₀ ⟶ X => g z) h
  change s (r z) ∈ U
  rw [← hw]
  exact hz

variable (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
  [IsClosedImmersion f₁] [IsClosedImmersion f₂]
  (s₁ : T ⟶ X₁) (s₂ : T ⟶ X₂)
  (h₁ : s₀ ≫ f₁ = r ≫ s₁) (h₂ : s₀ ≫ f₂ = r ≫ s₂)
  (U₁ : X₁.Opens) (U₂ : X₂.Opens) (ha₁ : IsAffineOpen U₁) (ha₂ : IsAffineOpen U₂)
  (hs₁ : ⊤ ≤ s₁ ⁻¹ᵁ U₁) (hs₂ : ⊤ ≤ s₂ ⁻¹ᵁ U₂)

include hr h₁ h₂ ha₁ ha₂ hs₁ hs₂ in
theorem exists_principal : ∃ a₁ : Γ(X₁, U₁), ∃ a₂ : Γ(X₂, U₂),
    (⊤ ≤ s₁ ⁻¹ᵁ X₁.basicOpen a₁) ∧ (⊤ ≤ s₂ ⁻¹ᵁ X₂.basicOpen a₂) ∧
      f₁ ⁻¹ᵁ X₁.basicOpen a₁ = f₂ ⁻¹ᵁ X₂.basicOpen a₂ := by
  let z : T₀ := Classical.ofNonempty
  have he₁ : f₁ (s₀ z) = s₁ (r z) := congrArg (fun g : T₀ ⟶ X₁ => g z) h₁
  have he₂ : f₂ (s₀ z) = s₂ (r z) := congrArg (fun g : T₀ ⟶ X₂ => g z) h₂
  have hz₁ : f₁ (s₀ z) ∈ U₁ := he₁ ▸ hs₁ (show r z ∈ (⊤ : T.Opens) from trivial)
  have hz₂ : f₂ (s₀ z) ∈ U₂ := he₂ ▸ hs₂ (show r z ∈ (⊤ : T.Opens) from trivial)
  obtain ⟨a₁, a₂, hy₁, hy₂, he⟩ :=
    CommonReductionPrincipalNeighborhood.exists_principal f₁ f₂ U₁ U₂ ha₁ ha₂ (s₀ z) hz₁ hz₂
  exact ⟨a₁, a₂, contains r hr s₀ f₁ s₁ h₁ _ z hy₁,
    contains r hr s₀ f₂ s₂ h₂ _ z hy₂, he⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CommonSectionPrincipalNeighborhood
