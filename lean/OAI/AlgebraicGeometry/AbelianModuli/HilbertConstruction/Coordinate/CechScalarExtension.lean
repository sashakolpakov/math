import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.CechComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.CechScalarLinearity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.ScalarExtensionKernel

/-! # Cech Scalar Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.CechScalarExtension

noncomputable section

/-! Scalar extension of the coordinate Čech complex is isomorphic to the actual complex of the extended homogeneous quotient. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem coordinateNonnegativeCechComplex_d (q : ℕ) :
    (CechComplex.coordinateNonnegativeCechComplex I).d q (q + 1) =
      ModuleCat.ofHom (HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
        (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) 0 (q + 1)) :=
  (Cochain.Head.CochainHead.tail_d (HilbertScheme.Presentations.ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex (σ := Fin (n + 1)) R
    (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) 0) q (q + 1)).trans
    (HilbertScheme.Presentations.ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex_d R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) 0 (q + 1))

def coordinateCechScalarExtensionIso :
    Cochain.ScalarExtensionKernel.cochainScalarExtension (CechComplex.coordinateNonnegativeCechComplex I) A ≅
      CechComplex.coordinateNonnegativeCechComplex (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => (CechScalarLinearity.coordinateCechTermScalarEquiv (A := A) I 0 (q + 1)).toModuleIso) (by
      intro i j hij
      change i + 1 = j at hij
      subst j
      apply ModuleCat.hom_ext
      ext x
      have hl := congrArg (fun k :
        (CechComplex.coordinateNonnegativeCechComplex (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)).X i ⟶
          (CechComplex.coordinateNonnegativeCechComplex (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)).X (i + 1) =>
        k (CechScalarLinearity.coordinateCechTermScalarEquiv (A := A) I 0 (i + 1) x))
        (coordinateNonnegativeCechComplex_d (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I) i)
      have hr := congrArg (fun k : (CechComplex.coordinateNonnegativeCechComplex I).X i ⟶
        (CechComplex.coordinateNonnegativeCechComplex I).X (i + 1) =>
        CechScalarLinearity.coordinateCechTermScalarEquiv (A := A) I 0 (i + 2) (k.hom.baseChange A x))
        (coordinateNonnegativeCechComplex_d I i)
      exact hl.trans
        ((HilbertScheme.Presentations.Coordinate.CechBaseChange.GradedHilbert.coordinateModuleCechTermBaseChangeEquiv_differential (S := A) I 0 (i + 1) x).symm.trans hr.symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.CechScalarExtension
