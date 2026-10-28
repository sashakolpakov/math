import Mathlib.Logic.Equiv.Defs

/-! # Equivalence Squares -/

namespace OAI.RepresentationTheory.Theta.Geometric.EquivalenceSquares

/-! Two exact comparison squares give the exact square between their
targets by composing through the common source. -/

theorem equivalence_between_apply_center {X₀ X₁ X₂ : Type*}
    (e₁ : X₀ ≃ X₁) (e₂ : X₀ ≃ X₂) (v : X₀) :
    (e₁.symm.trans e₂) (e₁ v) = e₂ v :=
  congrArg e₂ (e₁.symm_apply_apply v)

theorem equivalence_square_between {V₀ V₁ V₂ X₀ X₁ X₂ : Type*}
    (p₀ : V₀ → X₀) (p₁ : V₁ → X₁) (p₂ : V₂ → X₂)
    (e₁ : X₀ ≃ X₁) (e₂ : X₀ ≃ X₂) (t₁ : V₀ ≃ V₁) (t₂ : V₀ ≃ V₂)
    (h₁ : ∀ v, e₁ (p₀ v) = p₁ (t₁ v)) (h₂ : ∀ v, e₂ (p₀ v) = p₂ (t₂ v))
    (v : V₁) : (e₁.symm.trans e₂) (p₁ v) = p₂ ((t₁.symm.trans t₂) v) := by
  have h := (h₁ (t₁.symm v)).trans (congrArg p₁ (t₁.apply_symm_apply v))
  have hi : e₁.symm (p₁ v) = p₀ (t₁.symm v) :=
    (congrArg e₁.symm h).symm.trans (e₁.symm_apply_apply _)
  exact (congrArg e₂ hi).trans (h₂ (t₁.symm v))

end OAI.RepresentationTheory.Theta.Geometric.EquivalenceSquares
