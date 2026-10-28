
/-! # Existential Enrichment -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ExistentialEnrichment.CM

/-! Adjoin a uniformly available conclusion while preserving an existential witness. -/

universe u

theorem conjunction {α : Sort u} (P Q R : α → Prop)
    (h : ∃ x, P x ∧ Q x) (hr : ∀ x, R x) :
    ∃ x, P x ∧ Q x ∧ R x := by
  obtain ⟨x, hp, hq⟩ := h
  exact ⟨x, hp, hq, hr x⟩

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ExistentialEnrichment.CM
