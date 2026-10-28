import OAI.RepresentationTheory.Theta.Geometric.DifferenceBundleTranslation
import OAI.RepresentationTheory.Theta.Geometric.Pullback.SquareFrames
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.NormalizedLineIso
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeSmooth

/-! # Difference Translation -/

namespace OAI.RepresentationTheory.Theta.Geometric.Normalized.DifferenceTranslation

noncomputable section

/-! Zero-axis normalization singles out an actual difference-bundle
translation isomorphism. No choice of scalar remains in this comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem abelian_firstZeroSlice_appTop_bijective {g : ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) :
    Function.Bijective (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left.appTop := by
  have : ConnectedSpace A.scheme.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.scheme.hom
  have : ConnectedSpace (A.scheme ⊗ A.scheme).left :=
    inferInstanceAs (ConnectedSpace (Limits.pullback A.scheme.hom A.scheme.hom : Scheme))
  have : Smooth (A.scheme ⊗ A.scheme).hom := by dsimp; infer_instance
  have : IsProper (A.scheme ⊗ A.scheme).hom := by dsimp; infer_instance
  have : IsReduced A.scheme.left :=
    AlgebraicGeometry.Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced.reduced_of_smooth_field A.scheme.hom
  have : IsReduced (A.scheme ⊗ A.scheme).left :=
    AlgebraicGeometry.Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced.reduced_of_smooth_field (A.scheme ⊗ A.scheme).hom
  exact AlgebraicGeometry.AbelianScheme.CentralAction.LineEndRigidity.Construction.proper_pointed_appTop_bijective A.scheme (A.scheme ⊗ A.scheme)
    (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)) η[A.scheme].left (Over.w η[A.scheme])

def differenceTranslationNormalization {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) (p : Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ A.scheme)
    (e : ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback
      (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left).sheaf ≅
        AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left) :
    (((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback
      (DifferenceBundleTranslation.groupTranslation A.scheme p ⊗ₘ 𝟙 A.scheme).left).pullback
        (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left).sheaf ≅
          AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left :=
  Pullback.SquareFrames.pullbackSquareFrame (DifferenceBundleTranslation.groupTranslation A.scheme p ⊗ₘ 𝟙 A.scheme).left
    (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left
    (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left (DifferenceBundleTranslation.groupTranslation A.scheme p).left
    (congrArg Over.Hom.left (DifferenceBundleTranslation.firstTranslation_zeroSlice A.scheme p)).symm
    (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf e

theorem existsUnique_normalized_difference_translation {g : ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (p : Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ A.scheme)
    (hL : Nonempty ((L.pullback (DifferenceBundleTranslation.groupTranslation A.scheme p).left).sheaf ≅ L.sheaf))
    (e : ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback
      (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left).sheaf ≅
        AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left) :
    ∃! a : ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback
        (DifferenceBundleTranslation.groupTranslation A.scheme p ⊗ₘ 𝟙 A.scheme).left).sheaf ≅
          (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf,
      (Scheme.Modules.pullback (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left).map
        a.hom ≫ e.hom = (differenceTranslationNormalization A L p e).hom :=
  AlgebraicGeometry.AbelianScheme.CentralAction.NormalizedLineIso.Construction.existsUnique_normalized_line_iso _ (abelian_firstZeroSlice_appTop_bijective A)
    _ _ (DifferenceBundleTranslation.abelianDifferenceBundle_firstTranslation A L p hL)
    (differenceTranslationNormalization A L p e) e

end

end OAI.RepresentationTheory.Theta.Geometric.Normalized.DifferenceTranslation
