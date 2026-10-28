import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Polynomial

/-! # Eventual Saturated Equality -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.EventualSaturatedEquality.GradedHilbert

/-! Saturated homogeneous ideals are determined by any common tail of their degree relation modules. -/

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

theorem saturated_eq_of_eventual_degreeRelations
    (I J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal) (hJ : Hilbert.Polynomial.GradedHilbert.IsSaturated J.toIdeal)
    (N : ℕ) (h : ∀ d ≥ N, Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d = Hilbert.Polynomial.GradedHilbert.degreeRelations J.toIdeal d) : I = J := by
  apply HomogeneousIdeal.ext'
  intro d f hf
  constructor
  · intro hfI
    apply hJ f d hf
    refine ⟨N, fun g hg => ?_⟩
    have hm : (⟨g * f, hg.mul hf⟩ : Hilbert.Polynomial.GradedHilbert.grading R n (N + d)) ∈ Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal (N + d) :=
      I.toIdeal.mul_mem_left g hfI
    rw [h (N + d) (by omega)] at hm
    exact hm
  · intro hfJ
    apply hI f d hf
    refine ⟨N, fun g hg => ?_⟩
    have hm : (⟨g * f, hg.mul hf⟩ : Hilbert.Polynomial.GradedHilbert.grading R n (N + d)) ∈ Hilbert.Polynomial.GradedHilbert.degreeRelations J.toIdeal (N + d) :=
      J.toIdeal.mul_mem_left g hfJ
    rw [← h (N + d) (by omega)] at hm
    exact hm

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.EventualSaturatedEquality.GradedHilbert
