import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProductSegreMorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.AbsoluteTwistingBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SegreOver

/-! # Product Segre Twisting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProductSegreTwisting

noncomputable section

/-! The pullback of the actual Segre target's degree-one twisting bundle
along two section maps is the tensor product of their source line bundles. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S X : Scheme.{u}} (f : X ⟶ S) (L M : Line.Bundles.LineBundle X)
variable {n m d : ℕ}
variable (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
variable (t : Fin (m + 1) → (Line.Bundles.structureModule X ⟶ M.sheaf))
variable (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
variable (ht : ∀ x : X, ∃ j, x ∈ Ample.LineBundles.sectionNonvanishing (t j))
variable (e : Segre.ChartProjections.SegreProjectiveIndex.{u} n m ≃ Fin (d + 1))

def sectionProductSegreTwistingIso :
    ((AbsoluteTwistingBundle.affineProjectiveTwistingBundle Γ(S, ⊤) d).pullback
      ((ProductSegreMorphism.absoluteSectionProductMap f L M s t hs ht ≫
        Segre.ProjectiveIsomorphism.affineSegreEmbedding (CommRingCat.of Γ(S, ⊤)) n m) ≫
        (Projective.SpaceReindex.affineProjectiveSpaceReindexIso Γ(S, ⊤) e).hom.left)).sheaf ≅
      (L.tensor M).sheaf :=
  (Scheme.Modules.pullbackCongr (ProductSegreMorphism.absoluteSectionProductMap_segre f L M s t hs ht e)).app
    (AbsoluteTwistingBundle.affineProjectiveTwistingBundle Γ(S, ⊤) d).sheaf ≪≫
      AbsoluteTwistingBundle.sectionAbsoluteTwistingBundleIso f (Tensor.PairSectionFrames.tensorPairSectionFamily L M e s t)
        (Tensor.PairSectionFrames.tensorPairSectionFamily_covers L M e s t hs ht)

theorem absoluteSectionProductMap_standardSegre :
    ProductSegreMorphism.absoluteSectionProductMap f L M s t hs ht ≫
      (Affine.SegreOver.affineSegreStandardEmbedding (CommRingCat.of Γ(S, ⊤)) n m).left =
    SectionsProjectiveMorphism.sectionAbsoluteMorphism f
      (Tensor.PairSectionFrames.tensorPairSectionFamily L M (Grassmann.ProjectivePresentation.finiteProjectiveCoordinateEquiv (Segre.ChartProjections.SegreProjectiveIndex.{u} n m)) s t)
      (Tensor.PairSectionFrames.tensorPairSectionFamily_covers L M
        (Grassmann.ProjectivePresentation.finiteProjectiveCoordinateEquiv (Segre.ChartProjections.SegreProjectiveIndex.{u} n m)) s t hs ht) :=
  (Category.assoc _ _ _).symm.trans
    (ProductSegreMorphism.absoluteSectionProductMap_segre f L M s t hs ht
      (Grassmann.ProjectivePresentation.finiteProjectiveCoordinateEquiv (Segre.ChartProjections.SegreProjectiveIndex.{u} n m)))

def sectionProductStandardSegreTwistingIso :
    ((AbsoluteTwistingBundle.affineProjectiveTwistingBundle Γ(S, ⊤) (Affine.SegreOver.segreProjectiveDimension.{u} n m)).pullback
      (ProductSegreMorphism.absoluteSectionProductMap f L M s t hs ht ≫
        (Affine.SegreOver.affineSegreStandardEmbedding (CommRingCat.of Γ(S, ⊤)) n m).left)).sheaf ≅
      (L.tensor M).sheaf :=
  (Scheme.Modules.pullbackCongr (absoluteSectionProductMap_standardSegre f L M s t hs ht)).app
    (AbsoluteTwistingBundle.affineProjectiveTwistingBundle Γ(S, ⊤) (Affine.SegreOver.segreProjectiveDimension.{u} n m)).sheaf ≪≫
      AbsoluteTwistingBundle.sectionAbsoluteTwistingBundleIso f
        (Tensor.PairSectionFrames.tensorPairSectionFamily L M (Grassmann.ProjectivePresentation.finiteProjectiveCoordinateEquiv (Segre.ChartProjections.SegreProjectiveIndex.{u} n m)) s t)
        (Tensor.PairSectionFrames.tensorPairSectionFamily_covers L M
          (Grassmann.ProjectivePresentation.finiteProjectiveCoordinateEquiv (Segre.ChartProjections.SegreProjectiveIndex.{u} n m)) s t hs ht)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProductSegreTwisting
