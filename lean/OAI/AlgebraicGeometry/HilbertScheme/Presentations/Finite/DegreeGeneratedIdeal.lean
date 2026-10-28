import OAI.AlgebraicGeometry.HilbertScheme.Presentations.DegreeGeneratedIdeal
import Mathlib.RingTheory.Finiteness.Basic

/-! # Degree Generated Ideal -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.DegreeGeneratedIdeal.GradedHilbert

noncomputable section

/-! A finite relation module in one degree generates a finitely generated
homogeneous ideal over any coefficient ring. -/

universe u
variable {R : Type u} [CommRing R] {n : ℕ}

theorem degreeGeneratedIdeal_span_relations (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (N : ℕ) :
    (DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N).toIdeal =
      Ideal.span ((Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal N).map (Hilbert.Polynomial.GradedHilbert.grading R n N).subtype : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)) := by
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨hf, hI⟩
    exact ⟨⟨f, hf⟩, hI, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.property, hg⟩

theorem degreeGeneratedIdeal_fg (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (N : ℕ)
    (hfg : (Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal N).FG) : (DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N).toIdeal.FG := by
  rw [degreeGeneratedIdeal_span_relations]
  exact (hfg.map (Hilbert.Polynomial.GradedHilbert.grading R n N).subtype).span

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.DegreeGeneratedIdeal.GradedHilbert
