import Mathlib.RingTheory.Extension.Presentation.Submersive
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Presentation Dimension -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.PresentationDimension.Algebraic

noncomputable section

/-!
# Free-coordinate dimension of a submersive presentation

These finite-dimensional identities apply to the actual injection selecting
Jacobian columns. They identify the number of remaining coordinates with
mathlib's presentation dimension; they make no geometric dimension assertion.
-/

open scoped Classical

universe u v w t

variable {ι : Type w} {σ : Type t} [Fintype ι] [Fintype σ]

/-- The complement of the image of an injection has the expected finite size. -/
theorem card_complement_range (s : σ → ι) (hs : Function.Injective s) :
    Fintype.card {i : ι // i ∉ Set.range s} = Fintype.card ι - Fintype.card σ := by
  have hcard : Fintype.card (Set.range s) = Fintype.card σ :=
    (Fintype.card_congr (Equiv.ofInjective s hs)).symm
  simpa only [hcard] using Fintype.card_subtype_compl (fun i : ι => i ∈ Set.range s)

/-- Free coordinates and selected coordinates together account for every
coordinate, including the empty-index cases. -/
theorem card_complement_range_add (s : σ → ι) (hs : Function.Injective s) :
    Fintype.card {i : ι // i ∉ Set.range s} + Fintype.card σ = Fintype.card ι := by
  rw [card_complement_range s hs]
  exact Nat.sub_add_cancel (Fintype.card_le_of_injective s hs)

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- For a pre-submersive presentation, the number of unselected variables is
exactly its mathlib presentation dimension. -/
theorem card_free_variables_eq_dimension
    (P : Algebra.PreSubmersivePresentation R S ι σ) :
    Fintype.card {i : ι // i ∉ Set.range P.map} = P.dimension := by
  rw [card_complement_range P.map P.map_inj]
  simp only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card]

/-- The scalar coordinate space on the free variables has the same finite
dimension. This supplies the vector-space dimension for analytic chart work. -/
theorem finrank_free_variables_eq_dimension (K : Type*) [DivisionRing K]
    (P : Algebra.PreSubmersivePresentation R S ι σ) :
    Module.finrank K ({i : ι // i ∉ Set.range P.map} → K) = P.dimension := by
  rw [Module.finrank_pi, card_free_variables_eq_dimension P]

end

end OAI.AlgebraicGeometry.Foundations.Scheme.PresentationDimension.Algebraic
