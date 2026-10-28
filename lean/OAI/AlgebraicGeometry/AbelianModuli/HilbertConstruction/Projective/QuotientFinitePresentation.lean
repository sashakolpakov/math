import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ChartPresentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Flatness
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.Finiteness.Basic

/-! # Quotient Finite Presentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.QuotientFinitePresentation

noncomputable section

/-!
A finitely generated homogeneous ideal gives a finitely presented projective
closed family over an arbitrary coefficient ring. The proof checks the actual
standard affine charts, presented by the ideal together with X_i - 1.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ}
variable (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (hI : I.toIdeal.FG)
include hI

theorem quotientAffineChart_finitePresentation (i : Fin (n + 1)) :
    Algebra.FinitePresentation R
      (HomogeneousLocalization.Away (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
        (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (MvPolynomial.X i))) := by
  have hfg : (HilbertScheme.Presentations.Affine.ChartPresentation.GradedHilbert.affineChartIdeal I i).FG :=
    Submodule.FG.sup hI (Submodule.fg_span_singleton _)
  let : Algebra.FinitePresentation R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ HilbertScheme.Presentations.Affine.ChartPresentation.GradedHilbert.affineChartIdeal I i) :=
    Algebra.FinitePresentation.quotient hfg
  exact Algebra.FinitePresentation.equiv (HilbertScheme.Presentations.Affine.ChartPresentation.GradedHilbert.affineChartPresentationAlgEquiv I i)

theorem projectiveQuotient_locallyFinitePresentation :
    LocallyOfFinitePresentation (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) := by
  have : IsZariskiLocalAtSource @LocallyOfFinitePresentation.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation.{u})
      (Q := RingHom.FinitePresentation)
  let U := Proj.affineOpenCoverOfIrrelevantLESpan (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
    (fun i : Fin (n + 1) => HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (MvPolynomial.X i))
    (fun i => (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem (MvPolynomial.isHomogeneous_X R i))
    (fun _ => Nat.zero_lt_one) (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.quotient_irrelevant_le_span_variables I)
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFinitePresentation)
    U.openCover).mpr
  intro i
  change LocallyOfFinitePresentation (Proj.awayι (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
    (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (MvPolynomial.X i))
    ((HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem (MvPolynomial.isHomogeneous_X R i)) Nat.zero_lt_one ≫
    HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
  rw [HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap_away, LocallyOfFinitePresentation.SpecMap_iff]
  let := quotientAffineChart_finitePresentation I hI i
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.QuotientFinitePresentation
