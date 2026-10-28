import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.ProjectiveFlatFactorization
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.BaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.NoetherianModel

/-! # Model Cartesian Recovery -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations

noncomputable section

/-! The Noetherian local flat coefficient model recovers the original
projective scheme by an actual Cartesian square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {B A : Type u} [CommRing B] [CommRing A] [Algebra B A] {n : ℕ}

theorem Noetherian.ProjectiveFlatFactorization.GradedHilbert.NoetherianLocalFlatCoefficientModel.cartesian
    {I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading B n)} (M : Noetherian.ProjectiveFlatFactorization.GradedHilbert.NoetherianLocalFlatCoefficientModel (A := A) I) :
    ∃ g : Projective.Quotient.GradedHilbert.projectiveQuotient (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I) ⟶
        Projective.Quotient.GradedHilbert.projectiveQuotient (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := M.R) I),
      IsPullback g (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)))
        (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := M.R) I)))
        (Spec.map (CommRingCat.ofHom (algebraMap M.R A))) := by
  let J := Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := M.R) I
  have h : ∃ g : Projective.Quotient.GradedHilbert.projectiveQuotient (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) J) ⟶ Projective.Quotient.GradedHilbert.projectiveQuotient J,
      IsPullback g (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) J)))
        (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading J))
        (Spec.map (CommRingCat.ofHom (algebraMap M.R A))) :=
    ⟨Projective.CoefficientMap.GradedHilbert.projectiveCoefficientMap J, Projective.BaseChange.GradedHilbert.projectiveQuotient_isPullback J⟩
  let Q (L : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading A n)) : Prop :=
    ∃ g : Projective.Quotient.GradedHilbert.projectiveQuotient L ⟶ Projective.Quotient.GradedHilbert.projectiveQuotient J,
      IsPullback g (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading L))
        (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading J))
        (Spec.map (CommRingCat.ofHom (algebraMap M.R A)))
  exact (congrArg Q (Homogeneous.IdealTower.GradedHilbert.extendedHomogeneousIdeal_tower (C := M.R) (A := A) I)).mp h

theorem Flat.ModelCartesianRecovery.GradedHilbert.nativeEquationExtendedIdeal_flat
    {S : Scheme.{u}} (a : Spec (.of A) ⟶ S)
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a))
    (E : Intrinsic.AffineEquationModel.GradedHilbert.NativeAffineEquations a F) :
    Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (Intrinsic.AffineEquationModel.GradedHilbert.nativeEquationExtendedIdeal E B))) := by
  have : MorphismProperty.RespectsIso @Flat.{u} :=
    MorphismProperty.respectsIso_of_isStableUnderComposition
      (fun _ _ g (_ : IsIso g) => inferInstanceAs (Flat g))
  apply (MorphismProperty.cancel_left_of_respectsIso (P := @Flat)
    (Intrinsic.AffineEquationModel.GradedHilbert.nativeEquationModelIso E B).hom _).mp
  rw [Intrinsic.AffineEquationModel.GradedHilbert.nativeEquationModelIso_projection]
  exact F.property.1

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations
