import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EventualProjectiveTwistSections
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Existence

/-! # Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.Polynomial

noncomputable section

/-! The coordinate Hilbert polynomial equals the eventual dimension polynomial of actual global sections of the constructed projective twisting bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem projectiveTwistingSections_hilbertPolynomial_iff (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P ↔ ∃ B : ℕ, ∀ d : ℕ, B ≤ d →
      Module.Finite R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))).obj
        (Bundle.projectiveTwistingBundle I d).sheaf) ∧
      (Module.finrank R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))).obj
        (Bundle.projectiveTwistingBundle I d).sheaf) : ℚ) = P.eval (d : ℚ) := by
  obtain ⟨B, hB⟩ := EventualProjectiveTwistSections.projectiveTwistingSections_eventual_degree I
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨max B C, fun d hd => ⟨SectionsFinite.projectiveTwistingSections_finite I d, ?_⟩⟩
    obtain ⟨e⟩ := hB d ((le_max_left B C).trans hd)
    exact (congrArg (fun a : ℕ => (a : ℚ)) e.finrank_eq.symm).trans (hC d ((le_max_right B C).trans hd))
  · rintro ⟨C, hC⟩
    refine ⟨max B C, fun d hd => ?_⟩
    obtain ⟨e⟩ := hB d ((le_max_left B C).trans hd)
    exact (congrArg (fun a : ℕ => (a : ℚ)) e.finrank_eq).trans (hC d ((le_max_right B C).trans hd)).2

theorem projectiveTwistingSections_hilbertPolynomial_exists {K : Type u} [Field K]
    {m : ℕ} (J : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K m)) :
    ∃ P : Polynomial ℚ, ∃ B : ℕ, ∀ d : ℕ, B ≤ d →
      Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J))).obj
        (Bundle.projectiveTwistingBundle J d).sheaf) ∧
      (Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J))).obj
        (Bundle.projectiveTwistingBundle J d).sheaf) : ℚ) = P.eval (d : ℚ) := by
  obtain ⟨P, hP⟩ := HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert.exists_hilbertPolynomial J
  exact ⟨P, (projectiveTwistingSections_hilbertPolynomial_iff J P).mp hP⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.Polynomial
