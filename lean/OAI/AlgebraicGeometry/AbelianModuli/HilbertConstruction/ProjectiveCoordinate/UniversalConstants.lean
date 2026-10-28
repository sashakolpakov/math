import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.LocalRingPullbackConstants
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.GlobalFunctionsLocalCriterion

/-! # Universal Constants -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.UniversalConstants

noncomputable section

/-! Pointed proper smooth geometrically connected projective coordinate families over noetherian rings have only base global functions after arbitrary scheme base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem projectiveCoordinate_baseChange_globalFunctions_isIso
    {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
    [IsProper (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]
    [Smooth (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]
    [GeometricallyConnected (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]
    (x : Spec (.of R) ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
    (hx : x ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) = 𝟙 _)
    {T Y : Scheme.{u}} {a : Y ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)} {b : Y ⟶ T} {c : T ⟶ Spec (.of R)}
    (H : IsPullback a b (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) c) : IsIso b.appTop :=
  Universal.GlobalFunctionsLocalCriterion.universal_globalFunctions_isIso_of_localRingConstants
    (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) x hx
    (fun _ _ _ d => Coordinate.LocalRingPullbackConstants.projectiveCoordinate_localRingPullback_globalFunctions_isIso I x hx d) H

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.UniversalConstants
