import OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedCyclicWords
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! # Cyclic Word Basis -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.CyclicWordBasis.Construction

noncomputable section

/-! A cyclic subspace has a basis consisting of bounded-length words
in the original operators, without taking linear combinations. -/

open scoped Classical
open _root_.Module Set

theorem exists_cyclicWord_basis
    {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (A : ι → Module.End k V) (x : V) :
    ∃ (r : ℕ) (w : Fin r → List ι), r ≤ finrank k V ∧
      (∀ i, (w i).length ≤ finrank k V) ∧
      LinearIndependent k (fun i => BoundedCyclicWords.Construction.operatorWord A (w i) x) ∧
      Submodule.span k (Set.range (fun i => BoundedCyclicWords.Construction.operatorWord A (w i) x)) =
        BoundedCyclicWords.Construction.cyclicWordSpan A x (finrank k V) := by
  let W := {w : List ι // w.length ≤ finrank k V}
  let v : W → V := fun w => BoundedCyclicWords.Construction.operatorWord A w.val x
  obtain ⟨κ, a, _, hspan, hlin⟩ := exists_linearIndependent' k v
  let : Finite κ := hlin.finite
  let : Fintype κ := Fintype.ofFinite κ
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let w : Fin (Fintype.card κ) → List ι := fun i => (a (e i)).val
  have hli : LinearIndependent k (fun i => BoundedCyclicWords.Construction.operatorWord A (w i) x) := hlin.comp e e.injective
  refine ⟨Fintype.card κ, w, ?_, fun i => (a (e i)).property, hli, ?_⟩
  · simpa using hli.fintype_card_le_finrank
  · have hr : Set.range (fun i => BoundedCyclicWords.Construction.operatorWord A (w i) x) = Set.range (v ∘ a) := by
      exact e.surjective.range_comp (v ∘ a)
    rw [hr, hspan]
    apply congrArg (Submodule.span k)
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w.val, w.property, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.CyclicWordBasis.Construction
