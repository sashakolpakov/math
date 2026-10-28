import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CechFactorRestriction

/-! # Cech Cofaces -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CechCofaces

noncomputable section

/-! Negative-twist factor equivalences identify the actual Čech cofaces with graded chart restriction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem projectiveCechIndexFinset_delete_subset {q : ℕ}
    (a : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} (Fin (n + 1))) (q + 1)) (k : Fin (q + 2)) :
    Projective.CechIntersectionCoordinates.projectiveCechIndexFinset (a.delete k) ⊆ Projective.CechIntersectionCoordinates.projectiveCechIndexFinset a := by
  rw [Projective.CechIntersectionCoordinates.projectiveCechIndexFinset_delete]
  exact Finset.erase_subset _ _

theorem negativeTwistCechFactorEquiv_coface (d q : ℕ)
    (a : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} (Fin (n + 1))) (q + 1)) (k : Fin (q + 2))
    (x : Ordered.CoefficientCechTerms.coefficientCechFactor (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
      (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d).sheaf (Projective.CechCover.projectiveCechOpens I) q (a.delete k).val) :
    (CechTermEquivalence.negativeTwistCechFactorEquiv I d (q + 1) a
      ((Coefficient.ModulePresheaf.schemeModulePresheaf (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
        (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d).sheaf).map
          (((FormalCoproduct.mk _ (Projective.CechCover.projectiveCechOpens I)).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ a.val).op x)).val =
      HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (projectiveCechIndexFinset_delete_subset a k)
        (CechTermEquivalence.negativeTwistCechFactorEquiv I d q (a.delete k) x).val := by
  have he : ((FormalCoproduct.mk _ (Projective.CechCover.projectiveCechOpens I)).mapPower
      (SimplexCategory.δ k).toOrderHom.toFun).φ a.val =
    homOfLE (CechFactorRestriction.projectiveCechIntersection_le I (a.delete k) a (projectiveCechIndexFinset_delete_subset a k)) :=
    Subsingleton.elim _ _
  rw [he]
  exact CechFactorRestriction.negativeTwistCechFactorEquiv_restriction I d (a.delete k) a
    (projectiveCechIndexFinset_delete_subset a k) x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CechCofaces
