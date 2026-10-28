import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProductCoefficientMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProductSegreTwisting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.TwistingBundle

/-! # Section Product Segre -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.SectionProductSegre

noncomputable section

/-! The existing relative Segre presentation sends a pair of section maps
to the map of tensor-product sections, with its actual twisting bundle. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private theorem composite_map_triangle {C : Type*} [Category C]
    {X A B D Z : C} (a : X ⟶ A) (e : A ⟶ B) (q : B ⟶ Z)
    (c : A ⟶ D) (b : D ⟶ Z) (p : X ⟶ D) (r : X ⟶ Z)
    (he : e ≫ q = c ≫ b) (ha : a ≫ c = p) (hp : p ≫ b = r) :
    (a ≫ e) ≫ q = r := by
  rw [Category.assoc, he, ← Category.assoc, ha, hp]

variable {S X : Scheme.{u}} (f : X ⟶ S) (L M : Line.Bundles.LineBundle X) {n m : ℕ}
variable (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
variable (t : Fin (m + 1) → (Line.Bundles.structureModule X ⟶ M.sheaf))
variable (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
variable (ht : ∀ x : X, ∃ j, x ∈ Ample.LineBundles.sectionNonvanishing (t j))

def relativeSectionProductMap : Over.mk f ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n ⊗ Projective.ProjectivePresentations.projectiveSpaceOver S m :=
  lift (SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs) (SectionsProjectiveMorphism.sectionProjectiveMorphism f t ht)

theorem relativeSectionProductMap_coefficients :
    (relativeSectionProductMap f L M s t hs ht).left ≫ Projective.ProductCoefficientMap.relativeProjectiveProductCoefficientMap S n m =
      Section.ProductSegreMorphism.absoluteSectionProductMap f L M s t hs ht := by
  apply pullback.hom_ext
  · change ((relativeSectionProductMap f L M s t hs ht).left ≫
      Projective.ProductCoefficientMap.relativeProjectiveProductCoefficientMap S n m) ≫
      (fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n) (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) m)).left = _
    rw [Category.assoc, Projective.ProductCoefficientMap.relativeProjectiveProductCoefficientMap_fst, ← Category.assoc]
    have h : (relativeSectionProductMap f L M s t hs ht).left ≫
        (fst (Projective.ProjectivePresentations.projectiveSpaceOver S n) (Projective.ProjectivePresentations.projectiveSpaceOver S m)).left =
          (SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs).left := congrArg Over.Hom.left (lift_fst _ _)
    rw [h]
    exact (Section.ProjectiveBaseChange.sectionProjectiveMorphism_coefficientProjection f s hs).trans
      (Section.ProductSegreMorphism.absoluteSectionProductMap_fst f L M s t hs ht).symm
  · change ((relativeSectionProductMap f L M s t hs ht).left ≫
      Projective.ProductCoefficientMap.relativeProjectiveProductCoefficientMap S n m) ≫
      (snd (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n) (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) m)).left = _
    rw [Category.assoc, Projective.ProductCoefficientMap.relativeProjectiveProductCoefficientMap_snd, ← Category.assoc]
    have h : (relativeSectionProductMap f L M s t hs ht).left ≫
        (snd (Projective.ProjectivePresentations.projectiveSpaceOver S n) (Projective.ProjectivePresentations.projectiveSpaceOver S m)).left =
          (SectionsProjectiveMorphism.sectionProjectiveMorphism f t ht).left := congrArg Over.Hom.left (lift_snd _ _)
    rw [h]
    exact (Section.ProjectiveBaseChange.sectionProjectiveMorphism_coefficientProjection f t ht).trans
      (Section.ProductSegreMorphism.absoluteSectionProductMap_snd f L M s t hs ht).symm

theorem relativeSectionProductMap_segre :
    relativeSectionProductMap f L M s t hs ht ≫ (Projective.Products.projectiveSpaceProductPresentation S n m).embedding =
      SectionsProjectiveMorphism.sectionProjectiveMorphism f
        (Tensor.PairSectionFrames.tensorPairSectionFamily L M (Grassmann.ProjectivePresentation.finiteProjectiveCoordinateEquiv (Segre.ChartProjections.SegreProjectiveIndex.{u} n m)) s t)
        (Tensor.PairSectionFrames.tensorPairSectionFamily_covers L M
          (Grassmann.ProjectivePresentation.finiteProjectiveCoordinateEquiv (Segre.ChartProjections.SegreProjectiveIndex.{u} n m)) s t hs ht) := by
  apply Over.OverMorphism.ext
  apply (RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection_isPullback S (Affine.SegreOver.segreProjectiveDimension.{u} n m)).hom_ext
  · exact (composite_map_triangle
      (relativeSectionProductMap f L M s t hs ht).left
      (Projective.Products.projectiveSpaceProductPresentation S n m).embedding.left
      (RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection S (Affine.SegreOver.segreProjectiveDimension.{u} n m))
      (Projective.ProductCoefficientMap.relativeProjectiveProductCoefficientMap S n m)
      (Affine.SegreOver.affineSegreStandardEmbedding (CommRingCat.of Γ(S, ⊤)) n m).left
      (Section.ProductSegreMorphism.absoluteSectionProductMap f L M s t hs ht) _
      (Projective.ProductCoefficientMap.projectiveSpaceProductPresentation_coefficients S n m)
      (relativeSectionProductMap_coefficients f L M s t hs ht)
      (Section.ProductSegreTwisting.absoluteSectionProductMap_standardSegre f L M s t hs ht)).trans
        (Section.ProjectiveBaseChange.sectionProjectiveMorphism_coefficientProjection f _ _).symm
  · exact (relativeSectionProductMap f L M s t hs ht ≫
      (Projective.Products.projectiveSpaceProductPresentation S n m).embedding).w.trans
        (SectionsProjectiveMorphism.sectionProjectiveMorphism f _ _).w.symm

def relativeSectionProductSegreTwistingIso :
    ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S (Affine.SegreOver.segreProjectiveDimension.{u} n m)).pullback
      (relativeSectionProductMap f L M s t hs ht ≫
        (Projective.Products.projectiveSpaceProductPresentation S n m).embedding).left).sheaf ≅ (L.tensor M).sheaf :=
  (Scheme.Modules.pullbackCongr
    (congrArg Over.Hom.left (relativeSectionProductMap_segre f L M s t hs ht))).app
      (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S (Affine.SegreOver.segreProjectiveDimension.{u} n m)).sheaf ≪≫
    RelativeProjective.TwistingBundle.sectionProjectiveTwistingBundleIso f
      (Tensor.PairSectionFrames.tensorPairSectionFamily L M (Grassmann.ProjectivePresentation.finiteProjectiveCoordinateEquiv (Segre.ChartProjections.SegreProjectiveIndex.{u} n m)) s t)
      (Tensor.PairSectionFrames.tensorPairSectionFamily_covers L M
        (Grassmann.ProjectivePresentation.finiteProjectiveCoordinateEquiv (Segre.ChartProjections.SegreProjectiveIndex.{u} n m)) s t hs ht)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.SectionProductSegre
