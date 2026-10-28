import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Multiset.Bind

/-! # Multiset Enumeration -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.MultisetEnumeration

noncomputable section

/-! Reindex the original parameter multiset by an exhaustive subtype
enumeration. Equal target values remain separate entries throughout. -/

variable {A B X : Type*} [Fintype A] [Fintype B]

theorem univ_map_eq_sum_singletons (f : A → X) :
    Finset.univ.val.map f = ∑ a, ({f a} : Multiset X) := by
  simp only [Finset.sum_eq_multiset_sum]
  have h := Multiset.sum_map_singleton (Finset.univ.val.map f)
  simpa only [Multiset.map_map, Function.comp_def] using h.symm

theorem parameter_multiset_subtype (P : B → Prop) [DecidablePred P]
    (e : A ≃ {b // P b}) (f : A → X) :
    Finset.univ.val.map f =
      ∑ b, if h : P b then ({f (e.symm ⟨b, h⟩)} : Multiset X) else 0 := by
  rw [univ_map_eq_sum_singletons]
  let j : A → B := fun a => (e a).val
  have hj : Function.Injective j := Subtype.val_injective.comp e.injective
  apply Fintype.sum_of_injective j hj
  · intro b hb
    have hn : ¬P b := by
      intro h
      apply hb
      exact ⟨e.symm ⟨b, h⟩, congrArg Subtype.val (e.apply_symm_apply ⟨b, h⟩)⟩
    exact dite_eq_right hn
  · intro a
    dsimp only [j]
    rw [dite_eq_left (e a).property, e.symm_apply_apply]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.MultisetEnumeration
