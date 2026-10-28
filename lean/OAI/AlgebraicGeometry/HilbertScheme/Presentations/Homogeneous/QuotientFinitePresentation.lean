import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.PresentationBaseChange
import Mathlib.Algebra.Module.FinitePresentation

/-! # Quotient Finite Presentation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.QuotientFinitePresentation.GradedHilbert

noncomputable section

/-! Homogeneous degree quotients of finitely generated homogeneous ideals are finitely presented over arbitrary coefficient rings. -/

universe u z

variable {R : Type u} [CommRing R] {n : ℕ} {ι : Type z} [Fintype ι]

theorem homogeneousGeneratorsDegree_finitePresentation
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N) (d : ℕ) :
    Module.FinitePresentation R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal (d + N)) := by
  let f := RelationPresentation.GradedHilbert.homogeneousRelationPresentation g N hg d
  let : Module.Free R (Hilbert.Polynomial.GradedHilbert.grading R n (d + N)) := PresentationBaseChange.GradedHilbert.coordinateDegreeSpace_free (d + N)
  let : Module.FinitePresentation R (Hilbert.Polynomial.GradedHilbert.grading R n (d + N) ⧸ f.range) :=
    Module.finitePresentation_of_free_of_surjective f.range.mkQ f.range.mkQ_surjective (by
      rw [Submodule.ker_mkQ]
      exact Submodule.fg_range f)
  exact Module.FinitePresentation.of_equiv (RelationPresentation.GradedHilbert.homogeneousPresentationCokernelEquiv g N hg d)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.QuotientFinitePresentation.GradedHilbert
