import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectiveCoefficientBase
import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-! # Projective Adapter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter.ProjectiveCoefficients

noncomputable section

/-! HilbertConstruction's relative projective presentations over Spec C give native
projective presentations of the very same complex scheme. The adapter
uses actual coefficient-ring and pullback isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective

def complexSectionRingEquiv : Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) ≃+* ℂ :=
  (Scheme.ΓSpecIso (.of ℂ)).commRingCatIsoToRingEquiv

/-- The relative projective space of HilbertConstruction is the native complex Proj. -/
def complexProjectiveIso (n : ℕ) :
    (HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver Foundations.Scheme.ProjectiveSpace.complexBase n).left ≅ Foundations.Scheme.ProjectiveSpace.projectiveSpace n := by
  let : IsIso Foundations.Scheme.ProjectiveSpace.complexBase.toSpecΓ := IsAffine.affine
  have hfst : IsIso (pullback.fst (HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) n).hom
      Foundations.Scheme.ProjectiveSpace.complexBase.toSpecΓ) := pullback_fst_iso_of_right_iso _ _
  let e := @asIso Scheme _ _ _
    (pullback.fst (HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) n).hom Foundations.Scheme.ProjectiveSpace.complexBase.toSpecΓ) hfst
  exact e ≪≫ (ProjectiveCoefficientsId.ProjectiveCoefficients.schemeIso complexSectionRingEquiv n).symm

theorem complexProjectiveIso_base (n : ℕ) :
    (complexProjectiveIso n).hom ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n =
      (HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver Foundations.Scheme.ProjectiveSpace.complexBase n).hom := by
  let p := pullback.fst (HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) n).hom Foundations.Scheme.ProjectiveSpace.complexBase.toSpecΓ
  let q := pullback.snd (HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) n).hom Foundations.Scheme.ProjectiveSpace.complexBase.toSpecΓ
  have hc : (ProjectiveCoefficientsId.ProjectiveCoefficients.schemeIso complexSectionRingEquiv n).inv ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n =
      (HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) n).hom ≫
        Spec.map (Scheme.ΓSpecIso (.of ℂ)).inv :=
    ProjectiveCoefficientBase.ProjectiveCoefficients.schemeMap_base complexSectionRingEquiv.symm.toRingHom n
  change (p ≫ (ProjectiveCoefficientsId.ProjectiveCoefficients.schemeIso complexSectionRingEquiv n).inv) ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n = q
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => p ≫ z) hc).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ Spec.map (Scheme.ΓSpecIso (.of ℂ)).inv) pullback.condition).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun z => q ≫ z) (toSpecΓ_SpecMap_ΓSpecIso_inv (.of ℂ))).trans
              (Category.comp_id q))))))

def nativeProjectivePresentation {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} (P : HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) :
    Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom where
  ambientDimension := P.dimension
  embedding := P.embedding.left ≫ (complexProjectiveIso P.dimension).hom
  closedImmersion := inferInstanceAs
    (IsClosedImmersion (P.embedding.left ≫ (complexProjectiveIso P.dimension).hom))
  over_base := (Category.assoc _ _ _).trans
    ((congrArg (fun q => P.embedding.left ≫ q) (complexProjectiveIso_base P.dimension)).trans P.embedding.w)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter.ProjectiveCoefficients
