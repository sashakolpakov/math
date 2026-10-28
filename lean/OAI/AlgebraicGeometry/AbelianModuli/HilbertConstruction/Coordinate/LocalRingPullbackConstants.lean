import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.CoefficientBaseChangeConstants
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.GlobalFunctions

/-! # Local Ring Pullback Constants -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.LocalRingPullbackConstants

noncomputable section

/-! Every local-ring-valued base change of a pointed proper smooth geometrically connected projective coordinate family over a noetherian coefficient ring has only base functions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem projectiveCoordinate_localRingPullback_globalFunctions_isIso
    {R A : Type u} [CommRing R] [IsNoetherianRing R] [CommRing A] [IsLocalRing A]
    {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
    [IsProper (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]
    [Smooth (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]
    [GeometricallyConnected (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]
    (x : Spec (.of R) ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
    (hx : x ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) = 𝟙 _)
    (b : Spec (.of A) ⟶ Spec (.of R)) :
    IsIso (pullback.snd (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) b).appTop := by
  let φ : CommRingCat.of R ⟶ CommRingCat.of A := (Spec.fullyFaithful.preimage b).unop
  have he : Spec.map φ = b := Spec.fullyFaithful.map_preimage b
  let : Algebra R A := φ.hom.toAlgebra
  have h : IsIso (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I))).appTop :=
    Local.CoefficientBaseChangeConstants.localCoefficientBaseChange_globalFunctions_isIso I x hx
  have H := (Cartesian.GlobalFunctions.cartesian_globalFunctions_isIso_iff (HilbertScheme.Presentations.Projective.BaseChange.GradedHilbert.projectiveQuotient_isPullback (S := A) I)).mp h
  change IsIso (pullback.snd (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) (Spec.map φ)).appTop at H
  rw [he] at H
  exact H

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.LocalRingPullbackConstants
