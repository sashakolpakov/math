import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CechTermEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.ChartNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresheafRestrictionTransport

/-! # Cech Factor Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CechFactorRestriction

noncomputable section

/-! The actual negative-twist Čech factor equivalences commute with all coordinate-intersection restrictions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem projectiveCechIntersection_le {q r : ℕ}
    (a : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} (Fin (n + 1))) q)
    (b : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} (Fin (n + 1))) r)
    (h : Projective.CechIntersectionCoordinates.projectiveCechIndexFinset a ⊆ Projective.CechIntersectionCoordinates.projectiveCechIndexFinset b) :
    (∏ᶜ fun k : Fin (r + 1) ↦ Projective.CechCover.projectiveCechOpens I (b.val k)) ≤
      (∏ᶜ fun k : Fin (q + 1) ↦ Projective.CechCover.projectiveCechOpens I (a.val k)) := by
  rw [Projective.CechIntersectionCoordinates.projectiveCechIntersection_eq_chart I a, Projective.CechIntersectionCoordinates.projectiveCechIntersection_eq_chart I b]
  exact ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I h

theorem negativeTwistCechFactorEquiv_restriction (d : ℕ) {q r : ℕ}
    (a : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} (Fin (n + 1))) q)
    (b : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} (Fin (n + 1))) r)
    (h : Projective.CechIntersectionCoordinates.projectiveCechIndexFinset a ⊆ Projective.CechIntersectionCoordinates.projectiveCechIndexFinset b)
    (x : Ordered.CoefficientCechTerms.coefficientCechFactor (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
      (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d).sheaf (Projective.CechCover.projectiveCechOpens I) q a.val) :
    (CechTermEquivalence.negativeTwistCechFactorEquiv I d r b
      ((Coefficient.ModulePresheaf.schemeModulePresheaf (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
        (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d).sheaf).map
          (homOfLE (projectiveCechIntersection_le I a b h)).op x)).val =
      HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) h
        (CechTermEquivalence.negativeTwistCechFactorEquiv I d q a x).val := by
  let F := Coefficient.ModulePresheaf.schemeModulePresheaf (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
    (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d).sheaf
  let ea := F.mapIso (eqToIso (Projective.CechIntersectionCoordinates.projectiveCechIntersection_eq_chart I a).symm).op
  let eb := F.mapIso (eqToIso (Projective.CechIntersectionCoordinates.projectiveCechIntersection_eq_chart I b).symm).op
  let xa := ea.hom x
  let xb := eb.hom (F.map (homOfLE (projectiveCechIntersection_le I a b h)).op x)
  have hind := ChartNaturality.negativeTwistChartDegreeEquiv_independent I d (Projective.CechIntersectionCoordinates.projectiveCechIndexFinset b)
    (b.val 0).down (a.val 0).down (Projective.CechIntersectionCoordinates.projectiveCechIndexFinset_mem b 0)
    (h (Projective.CechIntersectionCoordinates.projectiveCechIndexFinset_mem a 0)) xb
  have ht := PresheafRestrictionTransport.modulePresheaf_restriction_transport_apply F
    (Projective.CechIntersectionCoordinates.projectiveCechIntersection_eq_chart I a) (Projective.CechIntersectionCoordinates.projectiveCechIntersection_eq_chart I b)
    (projectiveCechIntersection_le I a b h) (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I h) x
  have hr := ChartNaturality.negativeTwistChartDegreeEquiv_restriction I d h (a.val 0).down
    (Projective.CechIntersectionCoordinates.projectiveCechIndexFinset_mem a 0) xa
  exact (congrArg Subtype.val hind).trans ((congrArg (fun y ↦
    (ChartSections.negativeTwistChartDegreeEquiv I d (Projective.CechIntersectionCoordinates.projectiveCechIndexFinset b) (a.val 0).down
      (h (Projective.CechIntersectionCoordinates.projectiveCechIndexFinset_mem a 0)) y).val) ht).trans hr)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CechFactorRestriction
