import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.AffineEquationModel
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Noetherian Model -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.NoetherianModel.GradedHilbert

noncomputable section

/-! Every native affine projective family is the actual base change of a
proper finitely presented projective scheme over a finite coefficient algebra.
The coefficient algebra is noetherian when the chosen base ring is noetherian. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v
variable {S : Scheme.{u}} {R : Type u} [CommRing R] {n : ℕ}
variable {a : Spec (CommRingCat.of R) ⟶ S}
variable {F : Hilbert.Functor.Family (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)}
variable (E : AffineEquationModel.GradedHilbert.NativeAffineEquations a F) (B : Type v) [CommRing B] [Algebra B R]

def nativeEquationModelCoefficientMap : Projective.Quotient.GradedHilbert.projectiveQuotient (AffineEquationModel.GradedHilbert.nativeEquationExtendedIdeal E B) ⟶
    Projective.Quotient.GradedHilbert.projectiveQuotient (AffineEquationModel.GradedHilbert.nativeEquationModelIdeal E B) := by
  let : Algebra (AffineEquationModel.GradedHilbert.nativeEquationCoefficientRing E B) R :=
    (AffineEquationModel.GradedHilbert.nativeEquationCoefficientRing E B).val.toRingHom.toAlgebra
  exact Projective.CoefficientMap.GradedHilbert.projectiveCoefficientMap (AffineEquationModel.GradedHilbert.nativeEquationModelIdeal E B)

theorem nativeEquationModelCoefficient_isPullback :
    IsPullback (nativeEquationModelCoefficientMap E B)
      (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (AffineEquationModel.GradedHilbert.nativeEquationExtendedIdeal E B)))
      (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (AffineEquationModel.GradedHilbert.nativeEquationModelIdeal E B)))
      (Spec.map (CommRingCat.ofHom (AffineEquationModel.GradedHilbert.nativeEquationCoefficientRing E B).val.toRingHom)) := by
  let : Algebra (AffineEquationModel.GradedHilbert.nativeEquationCoefficientRing E B) R :=
    (AffineEquationModel.GradedHilbert.nativeEquationCoefficientRing E B).val.toRingHom.toAlgebra
  exact Projective.BaseChange.GradedHilbert.projectiveQuotient_isPullback (AffineEquationModel.GradedHilbert.nativeEquationModelIdeal E B)

def nativeEquationModelMap : F.val.subscheme ⟶ Projective.Quotient.GradedHilbert.projectiveQuotient (AffineEquationModel.GradedHilbert.nativeEquationModelIdeal E B) :=
  (AffineEquationModel.GradedHilbert.nativeEquationModelIso E B).hom ≫ nativeEquationModelCoefficientMap E B

theorem nativeEquationModel_isPullback :
    IsPullback (nativeEquationModelMap E B) (Hilbert.Functor.familyProjection (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) F.val)
      (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (AffineEquationModel.GradedHilbert.nativeEquationModelIdeal E B)))
      (Spec.map (CommRingCat.ofHom (AffineEquationModel.GradedHilbert.nativeEquationCoefficientRing E B).val.toRingHom)) := by
  let p : F.val.subscheme ⟶ Spec (CommRingCat.of R) :=
    Hilbert.Functor.familyProjection (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) F.val
  have h : IsPullback (AffineEquationModel.GradedHilbert.nativeEquationModelIso E B).hom p
      (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (AffineEquationModel.GradedHilbert.nativeEquationExtendedIdeal E B))) (𝟙 (Spec (CommRingCat.of R))) :=
    IsPullback.of_horiz_isIso ⟨(AffineEquationModel.GradedHilbert.nativeEquationModelIso_projection E B).trans (Category.comp_id _).symm⟩
  change IsPullback ((AffineEquationModel.GradedHilbert.nativeEquationModelIso E B).hom ≫ nativeEquationModelCoefficientMap E B) p _ _
  simpa only [Category.id_comp] using h.paste_horiz (nativeEquationModelCoefficient_isPullback E B)

theorem nativeEquationModel_locallyOfFinitePresentation [IsNoetherianRing B] :
    LocallyOfFinitePresentation (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (AffineEquationModel.GradedHilbert.nativeEquationModelIdeal E B))) := by
  have : IsProper (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (AffineEquationModel.GradedHilbert.nativeEquationModelIdeal E B))) :=
    Projective.Properness.GradedHilbert.projectiveQuotient_proper _
  infer_instance

theorem native_affine_noetherian_model [IsNoetherianRing B] (a : Spec (CommRingCat.of R) ⟶ S)
    (F : Hilbert.Functor.Family (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)) :
    ∃ (C : Subalgebra B R), Algebra.FiniteType B C ∧ IsNoetherianRing C ∧
      ∃ (Z : Scheme.{u}) (p : Z ⟶ Spec (CommRingCat.of C)), IsProper p ∧ LocallyOfFinitePresentation p ∧
        ∃ q : F.val.subscheme ⟶ Z,
          IsPullback q (Hilbert.Functor.familyProjection (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) F.val) p
            (Spec.map (CommRingCat.ofHom C.val.toRingHom)) := by
  let E := AffineEquationModel.GradedHilbert.nativeAffineEquations a F
  refine ⟨AffineEquationModel.GradedHilbert.nativeEquationCoefficientRing E B, inferInstance, inferInstance,
    Projective.Quotient.GradedHilbert.projectiveQuotient (AffineEquationModel.GradedHilbert.nativeEquationModelIdeal E B), Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (AffineEquationModel.GradedHilbert.nativeEquationModelIdeal E B)),
    Projective.Properness.GradedHilbert.projectiveQuotient_proper _, nativeEquationModel_locallyOfFinitePresentation E B,
    nativeEquationModelMap E B, nativeEquationModel_isPullback E B⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.NoetherianModel.GradedHilbert
