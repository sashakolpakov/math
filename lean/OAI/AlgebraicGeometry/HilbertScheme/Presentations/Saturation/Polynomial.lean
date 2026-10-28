import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Saturation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Existence

/-! # Polynomial -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.Polynomial.GradedHilbert

noncomputable section

/-! The actual projective saturation preserves the eventual Hilbert function and Hilbert polynomial. -/

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}

theorem projectiveSaturation_eventual_hilbertFunction (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    ∃ N : ℕ, ∀ d ≥ N,
      Hilbert.Polynomial.GradedHilbert.hilbertFunction (Projective.Saturation.GradedHilbert.projectiveSaturation I).toIdeal d = Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d := by
  obtain ⟨N, hN⟩ := Projective.Saturation.GradedHilbert.projectiveSaturation_eventual_degreeRelations I
  refine ⟨N, fun d hd => ?_⟩
  exact (Submodule.quotEquivOfEq _ _ (hN d hd)).finrank_eq

theorem projectiveSaturation_hasHilbertPolynomial_iff
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (P : Polynomial ℚ) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Projective.Saturation.GradedHilbert.projectiveSaturation I).toIdeal P ↔ Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P := by
  obtain ⟨N, hN⟩ := projectiveSaturation_eventual_hilbertFunction I
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨max N B, fun d hd => ?_⟩
    rw [← hN d ((le_max_left _ _).trans hd)]
    exact hB d ((le_max_right _ _).trans hd)
  · rintro ⟨B, hB⟩
    refine ⟨max N B, fun d hd => ?_⟩
    rw [hN d ((le_max_left _ _).trans hd)]
    exact hB d ((le_max_right _ _).trans hd)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.Polynomial.GradedHilbert
