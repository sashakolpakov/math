import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CechCofaces
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PositiveTwist.CechFactorRestriction

/-! # Cech Cofaces -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PositiveTwist.CechCofaces

noncomputable section

/-! Nonnegative-twist factor equivalences identify the actual Čech cofaces with graded chart restriction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem positiveTwistCechFactorEquiv_coface (d q : ℕ)
    (a : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} (Fin (n + 1))) (q + 1)) (k : Fin (q + 2))
    (x : Ordered.CoefficientCechTerms.coefficientCechFactor (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
      (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf (Projective.CechCover.projectiveCechOpens I) q (a.delete k).val) :
    (CechTermEquivalence.positiveTwistCechFactorEquiv I d (q + 1) a
      ((Coefficient.ModulePresheaf.schemeModulePresheaf (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
        (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf).map
          (((FormalCoproduct.mk _ (Projective.CechCover.projectiveCechOpens I)).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ a.val).op x)).val =
      HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (NegativeTwist.CechCofaces.projectiveCechIndexFinset_delete_subset a k)
        (CechTermEquivalence.positiveTwistCechFactorEquiv I d q (a.delete k) x).val := by
  have he : ((FormalCoproduct.mk _ (Projective.CechCover.projectiveCechOpens I)).mapPower
      (SimplexCategory.δ k).toOrderHom.toFun).φ a.val =
    homOfLE (NegativeTwist.CechFactorRestriction.projectiveCechIntersection_le I (a.delete k) a (NegativeTwist.CechCofaces.projectiveCechIndexFinset_delete_subset a k)) :=
    Subsingleton.elim _ _
  rw [he]
  exact CechFactorRestriction.positiveTwistCechFactorEquiv_restriction I d (a.delete k) a
    (NegativeTwist.CechCofaces.projectiveCechIndexFinset_delete_subset a k) x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PositiveTwist.CechCofaces
