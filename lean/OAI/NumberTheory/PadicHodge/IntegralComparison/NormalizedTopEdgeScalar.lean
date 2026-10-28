import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Hom.Instances

/-! # Normalized Top Edge Scalar -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NormalizedTopEdgeScalar

/-! A normalized top-edge class detects the degree action without
requiring the edge to be injective or a trace on its quotient. -/

variable {T₁ T₂ C H : Type*}
  [AddCommGroup T₁] [AddCommGroup T₂] [AddCommGroup C] [AddCommGroup H]
  (e₁ : T₁ →+ H) (e₂ : T₂ →+ H) (t₁ : T₁ ≃+ C) (t₂ : T₂ ≃+ C)

theorem normalized_of_generator (c : C) (hc : ∀ z : C, ∃ n : ℕ, n • c = z)
    (h : e₁ (t₁.symm c) = e₂ (t₂.symm c)) (z : C) :
    e₁ (t₁.symm z) = e₂ (t₂.symm z) := by
  obtain ⟨n, rfl⟩ := hc z
  simp only [map_nsmul, h]

theorem scalar (f : H →+ H) (a : T₂ →+ T₁) (d : ℕ)
    (he : Function.Surjective e₂)
    (hn : ∀ z : C, e₁ (t₁.symm z) = e₂ (t₂.symm z))
    (ht : ∀ z : T₂, t₁ (a z) = d • t₂ z)
    (ha : ∀ z : T₂, f (e₂ z) = e₁ (a z)) (x : H) : f x = d • x := by
  obtain ⟨z, rfl⟩ := he x
  have hz : a z = t₁.symm (d • t₂ z) := by
    apply t₁.injective
    rw [t₁.apply_symm_apply, ht]
  rw [ha, hz, hn]
  simp only [map_nsmul, t₂.symm_apply_apply]

theorem scalar_of_generator (f : H →+ H) (a : T₂ →+ T₁) (d : ℕ)
    (he : Function.Surjective e₂) (c : C)
    (hc : ∀ z : C, ∃ n : ℕ, n • c = z)
    (hn : e₁ (t₁.symm c) = e₂ (t₂.symm c))
    (ht : ∀ z : T₂, t₁ (a z) = d • t₂ z)
    (ha : ∀ z : T₂, f (e₂ z) = e₁ (a z)) (x : H) : f x = d • x :=
  scalar e₁ e₂ t₁ t₂ f a d he (normalized_of_generator e₁ e₂ t₁ t₂ c hc hn) ht ha x

end OAI.NumberTheory.PadicHodge.IntegralComparison.NormalizedTopEdgeScalar
