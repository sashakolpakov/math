import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FunctorReturnIdentity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.DataEmbeddingReplacement
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineCoordinateSectionData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Canonical.QuotientSectionMorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SectionDataBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.PresentationSectionData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationAmpleBundle

/-! # Projective Section Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Canonical.ProjectiveSectionData

noncomputable section

/-! Every existing projective presentation has canonical section data for
its pulled-back O(1). The construction follows the quotient coordinates,
the affine standard space, and then the native arbitrary-base comparison. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def identityProjectivePresentation (S : Scheme.{u}) (n : ℕ) :
    Projective.ProjectivePresentations.ProjectivePresentation (Projective.ProjectivePresentations.projectiveSpaceOver S n) where
  dimension := n
  embedding := 𝟙 _
  closedImmersion := inferInstanceAs (IsClosedImmersion (𝟙 (Projective.ProjectivePresentations.projectiveSpaceOver S n).left))

private def affineCoordinateSectionData_baseChange
    (R : CommRingCat.{u}) (n : ℕ) (T : Scheme.{u}) (f : T ⟶ Spec R) :
    ((AffineCoordinateSectionData.bundledAffineCoordinatePresentation R n).baseChange f).SectionData
      ((Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n).pullback
        (CategoryTheory.Limits.pullback.fst (AffineCoordinateSectionData.bundledAffineProjectiveSpace R n).hom f)) :=
  (AffineCoordinateSectionData.bundledAffineCoordinateSectionData R n).baseChange f

private theorem mapIso_symm_trans_hom
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} {Z : D} (e : X ≅ Y) (k : Z ≅ F.obj X) :
    (F.mapIso e.symm ≪≫ k.symm).hom = F.map e.inv ≫ k.inv := rfl

private abbrev affineCoordinatePresentation_return_hom (S : Scheme.{u}) (n : ℕ) :=
  (mapIso_symm_trans_hom (Over.pullback S.toSpecΓ)
    (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso Γ(S, ⊤) n)
    (Projective.SpaceBaseChange.projectiveSpaceOverBaseChangeIso S.toSpecΓ n)).symm

private abbrev nativeCoordinateData (S : Scheme.{u}) (n : ℕ) :=
  affineCoordinateSectionData_baseChange Γ(S, ⊤) n S S.toSpecΓ

private theorem relativeCoordinateEmbeddingEq (S : Scheme.{u}) (n : ℕ) :
    𝟙 (Projective.ProjectivePresentations.projectiveSpaceOver S n) =
      SectionsProjectiveMorphism.sectionProjectiveMorphism (n := n) (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom
        (nativeCoordinateData S n).sections (nativeCoordinateData S n).covers := by
  let D := nativeCoordinateData S n
  exact (((Projective.PresentationBaseChange.nativeAffineProjectivePresentation Γ(S, ⊤) n).baseChangeIso_hom S.toSpecΓ).symm.trans
    (Projective.SpecIsoProjections.projectiveCoefficientReturnIso_hom S n)).symm.trans D.embedding_eq

def relativeCoordinateSectionData (S : Scheme.{u}) (n : ℕ) :
    (identityProjectivePresentation S n).SectionData (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n) where
  sections := (nativeCoordinateData S n).sections
  covers := (nativeCoordinateData S n).covers
  embedding_eq := relativeCoordinateEmbeddingEq S n

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation.canonicalSectionData {S : Scheme.{u}} {X : Over S}
    (P : Projective.ProjectivePresentations.ProjectivePresentation X) : P.SectionData P.ampleLineBundle := by
  let D := (relativeCoordinateSectionData S P.dimension).precomp P.embedding
  have h : ((identityProjectivePresentation S P.dimension).precomp P.embedding).embedding = P.embedding :=
    Category.comp_id P.embedding
  exact ⟨D.sections, D.covers, h.symm.trans D.embedding_eq⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Canonical.ProjectiveSectionData
