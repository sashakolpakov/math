import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CechDifferentialCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.Head
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.CechComplex

/-! # Cech Complex Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CechComplexIsomorphism

noncomputable section

/-! The actual negative-twist projective Čech complex is isomorphic to the nonaugmented graded localization complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.CechComplex.ProjectiveCech

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def negativeTwistCechComplexIso (d : ℕ) :
    (Projective.CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d).sheaf ≅
      Cochain.Head.CochainHead.tail (HilbertScheme.Presentations.ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
        (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (-(d : ℤ))) :=
  HomologicalComplex.Hom.isoOfComponents (fun q ↦ (CechTermEquivalence.negativeTwistCechTermEquiv I d q).toModuleIso) (by
    intro i j hij
    change i + 1 = j at hij
    subst j
    rw [Cochain.Head.CochainHead.tail_d, HilbertScheme.Presentations.ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex_d]
    change (CechTermEquivalence.negativeTwistCechTermEquiv I d i).toModuleIso.hom ≫
        ModuleCat.ofHom (HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
          (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (-(d : ℤ)) (i + 1)) =
      (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
        (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d).sheaf (Projective.CechCover.projectiveCechOpens I)).d i (i + 1) ≫
          (CechTermEquivalence.negativeTwistCechTermEquiv I d (i + 1)).toModuleIso.hom
    rw [Ordered.CoefficientCechComplex.orderedCoefficientCechComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (CechDifferentialCompatibility.negativeTwistCechTermEquiv_differential I d i x).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CechComplexIsomorphism
