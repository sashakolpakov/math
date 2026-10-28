import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Has

/-! # Construction Projective Presentation Comparison -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations

noncomputable section

/-! Exact comparison of the HilbertConstruction and Presentations projective-space conventions,
preserving closed embeddings and the structure maps to the base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem Hilbert.ConstructionProjectivePresentationComparison.Core.e33_affineProjectiveSpace_map (R : CommRingCat.{u}) (n : ℕ) :
    (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n).hom = Has.Core.projectiveSpaceMap R n := by
  change Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom
    (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.degreeZeroConstants R n).toRingHom) =
      Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom (algebraMap R _))
  congr 2

def Hilbert.ConstructionProjectivePresentationComparison.Core.e33ProjectiveSpaceIso (S : Scheme.{u}) (n : ℕ) :
    AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S n ≅ Over.mk (Has.Core.projectiveSpaceProjection S n) :=
  Over.isoMk (pullback.congrHom (Hilbert.ConstructionProjectivePresentationComparison.Core.e33_affineProjectiveSpace_map Γ(S, ⊤) n) rfl)
    (by
      change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
      exact pullback.lift_snd _ _ _)

theorem Hilbert.ConstructionProjectivePresentationComparison.Core.e33ProjectiveSpaceIso_hom_fst (S : Scheme.{u}) (n : ℕ) :
    (Hilbert.ConstructionProjectivePresentationComparison.Core.e33ProjectiveSpaceIso S n).hom.left ≫ pullback.fst (Has.Core.projectiveSpaceMap Γ(S, ⊤) n) S.toSpecΓ =
      pullback.fst (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ :=
  pullback.lift_fst _ _ _

theorem Hilbert.ConstructionProjectivePresentationComparison.Core.e33ProjectiveSpaceIso_inv_fst (S : Scheme.{u}) (n : ℕ) :
    (Hilbert.ConstructionProjectivePresentationComparison.Core.e33ProjectiveSpaceIso S n).inv.left ≫
      pullback.fst (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ =
        pullback.fst (Has.Core.projectiveSpaceMap Γ(S, ⊤) n) S.toSpecΓ :=
  (Iso.inv_comp_eq ((Over.forget S).mapIso (Hilbert.ConstructionProjectivePresentationComparison.Core.e33ProjectiveSpaceIso S n))).mpr
    (Hilbert.ConstructionProjectivePresentationComparison.Core.e33ProjectiveSpaceIso_hom_fst S n).symm

def Has.Core.ProjectivePresentation.toHilbertConstruction {S : Scheme.{u}} {X : Over S}
    (B : Has.Core.ProjectivePresentation X) : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X where
  dimension := B.dimension
  embedding := Over.homMk B.embedding B.over_base ≫ (Hilbert.ConstructionProjectivePresentationComparison.Core.e33ProjectiveSpaceIso S B.dimension).inv
  closedImmersion := by
    let := B.closed
    let : IsIso (Hilbert.ConstructionProjectivePresentationComparison.Core.e33ProjectiveSpaceIso S B.dimension).inv.left :=
      ((Over.forget S).mapIso (Hilbert.ConstructionProjectivePresentationComparison.Core.e33ProjectiveSpaceIso S B.dimension).symm).isIso_hom
    change IsClosedImmersion (B.embedding ≫ (Hilbert.ConstructionProjectivePresentationComparison.Core.e33ProjectiveSpaceIso S B.dimension).inv.left)
    infer_instance

def Has.Core.ProjectivePresentation.ofHilbertConstruction {S : Scheme.{u}} {X : Over S}
    (B : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) : Has.Core.ProjectivePresentation X where
  dimension := B.dimension
  embedding := (B.embedding ≫ (Hilbert.ConstructionProjectivePresentationComparison.Core.e33ProjectiveSpaceIso S B.dimension).hom).left
  closed := by
    let : IsIso (Hilbert.ConstructionProjectivePresentationComparison.Core.e33ProjectiveSpaceIso S B.dimension).hom.left :=
      ((Over.forget S).mapIso (Hilbert.ConstructionProjectivePresentationComparison.Core.e33ProjectiveSpaceIso S B.dimension)).isIso_hom
    change IsClosedImmersion (B.embedding.left ≫ (Hilbert.ConstructionProjectivePresentationComparison.Core.e33ProjectiveSpaceIso S B.dimension).hom.left)
    infer_instance
  over_base := (B.embedding ≫ (Hilbert.ConstructionProjectivePresentationComparison.Core.e33ProjectiveSpaceIso S B.dimension).hom).w

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations
