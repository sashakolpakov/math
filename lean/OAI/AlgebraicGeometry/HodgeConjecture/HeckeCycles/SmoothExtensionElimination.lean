import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-! # Smooth Extension Elimination -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.SmoothExtensionElimination.CM.RepresentationPullback

/-! Smooth vector stabilizers pull back along a continuous group map. -/

theorem smooth {G H k V : Type*} [Group G] [Group H] [TopologicalSpace G]
    [TopologicalSpace H] [Field k] [AddCommGroup V] [Module k V]
    (ρ : H →* (V ≃ₗ[k] V)) (hρ : ∀ v : V, IsOpen {g | ρ g v = v})
    (f : G →* H) (hf : Continuous f) (σ : G →* (V ≃ₗ[k] V))
    (he : σ = ρ.comp f) (v : V) : IsOpen {g | σ g v = v} := by
  subst σ
  exact (hρ v).preimage hf

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.SmoothExtensionElimination.CM.RepresentationPullback

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.SmoothExtensionElimination.CM

/-! Eliminate a full smooth-extension conclusion without expanding its
concrete source representation inside the elimination tactic. -/

theorem apply {G R k V : Type*} [Group G] [Group R] [TopologicalSpace G]
    [Field k] [AddCommGroup V] [Module k V]
    (r : R →* G) (σ : R →* (V ≃ₗ[k] V))
    (h : ∃ ρ : G →* (V ≃ₗ[k] V),
      (∀ v : V, IsOpen {g | ρ g v = v}) ∧ ρ.comp r = σ)
    {P : Prop}
    (hp : ∀ ρ : G →* (V ≃ₗ[k] V),
      (∀ v : V, IsOpen {g | ρ g v = v}) → ρ.comp r = σ → P) : P := by
  obtain ⟨ρ, hρ, hr⟩ := h
  exact hp ρ hρ hr

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.SmoothExtensionElimination.CM

end

end OAI
