import OAI.NumberTheory.Quaternion.Arithmetic.FiniteLieIdeals
import Mathlib.Topology.Connected.Clopen

/-! # Finite Connected Action -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.FiniteConnectedAction

noncomputable section

/-! A map from a connected space to a finite set is constant when every
fiber is closed. This will apply to the algebraic adjoint action on the
finite collection of Lie ideals. -/

open scoped Classical
open Set

theorem finite_closed_fibers_constant
    {X α : Type*} [TopologicalSpace X] [PreconnectedSpace X] [Finite α]
    (f : X → α) (hf : ∀ a, IsClosed {x : X | f x = a}) (x₀ x : X) : f x = f x₀ := by
  let s : Set X := {y | f y = f x₀}
  have he : sᶜ = ⋃ a : {a : α // a ≠ f x₀}, {y : X | f y = a.val} := by
    ext y
    constructor
    · intro hy
      exact mem_iUnion.mpr ⟨⟨f y, hy⟩, rfl⟩
    · intro hy
      obtain ⟨a, ha⟩ := mem_iUnion.mp hy
      exact fun hs => a.property (ha.symm.trans hs)
  have hsc : IsClosed sᶜ := by
    rw [he]
    exact isClosed_iUnion_of_finite (fun a => hf a.val)
  have hs : IsClopen s := ⟨hf (f x₀), isClosed_compl_iff.mp hsc⟩
  have hsu : s = univ := hs.eq_univ ⟨x₀, rfl⟩
  have hx : x ∈ s := by rw [hsu]; trivial
  exact hx

end

end OAI.NumberTheory.Quaternion.Arithmetic.FiniteConnectedAction
