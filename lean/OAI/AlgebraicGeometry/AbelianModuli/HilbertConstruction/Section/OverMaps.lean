import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.SectionProductSegre
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ExternalTensorBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectivePrecomposition

/-! # Over Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.OverMaps

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
universe u

def sectionProjectiveOverMap {S : Scheme.{u}} (X : Over S) {M : X.left.Modules} {n : ℕ}
    (s : Fin (n + 1) → (Line.Bundles.structureModule X.left ⟶ M))
    (hs : ∀ x : X.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) :
    X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n :=
  Over.homMk (SectionsProjectiveMorphism.sectionProjectiveMorphism X.hom s hs).left (SectionsProjectiveMorphism.sectionProjectiveMorphism X.hom s hs).w

theorem sectionProjectiveOverMap_eq {S : Scheme.{u}} (X : Over S) {M : X.left.Modules} {n : ℕ}
    (s : Fin (n + 1) → (Line.Bundles.structureModule X.left ⟶ M))
    (hs : ∀ x : X.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) :
    sectionProjectiveOverMap X s hs = SectionsProjectiveMorphism.sectionProjectiveMorphism X.hom s hs := rfl

theorem sectionProjectiveOverMap_precomp {S : Scheme.{u}} {X Y : Over S} (a : X ⟶ Y)
    (L : Line.Bundles.LineBundle Y.left) {n : ℕ}
    (s : Fin (n + 1) → (Line.Bundles.structureModule Y.left ⟶ L.sheaf))
    (hs : ∀ y : Y.left, ∃ i, y ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ht : ∀ x : X.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection a.left (s i))) :
    a ≫ sectionProjectiveOverMap Y s hs =
      sectionProjectiveOverMap X (M := (L.pullback a.left).sheaf) (fun i => Ample.LineBundles.pullbackSection a.left (s i)) ht := by
  convert (ProjectivePrecomposition.sectionProjectiveMorphism_precomp a L s hs ht) using 2 <;> rfl

private theorem overSection_coefficients {S : Scheme.{u}} (X : Over S) {M : X.left.Modules} {n : ℕ}
    (s : Fin (n + 1) → (Line.Bundles.structureModule X.left ⟶ M))
    (hs : ∀ x : X.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) :
    (sectionProjectiveOverMap X s hs).left ≫ RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection S n =
      SectionsProjectiveMorphism.sectionAbsoluteMorphism X.hom s hs :=
  ProjectiveBaseChange.sectionProjectiveMorphism_coefficientProjection X.hom s hs

private theorem overProduct_coefficients {S : Scheme.{u}} (X : Over S)
    (L M : Line.Bundles.LineBundle X.left) {n m : ℕ}
    (s : Fin (n + 1) → (Line.Bundles.structureModule X.left ⟶ L.sheaf))
    (t : Fin (m + 1) → (Line.Bundles.structureModule X.left ⟶ M.sheaf))
    (hs : ∀ x : X.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ht : ∀ x : X.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (t i)) :
    (lift (sectionProjectiveOverMap X s hs) (sectionProjectiveOverMap X t ht)).left ≫
      Projective.ProductCoefficientMap.relativeProjectiveProductCoefficientMap S n m = ProductSegreMorphism.absoluteSectionProductMap X.hom L M s t hs ht :=
  Relative.SectionProductSegre.relativeSectionProductMap_coefficients X.hom L M s t hs ht

private theorem overSegre_coefficients (S : Scheme.{u}) (n m : ℕ) :
    (Projective.Products.nativeSegreProductEmbedding S n m).left ≫
      RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection S (Affine.SegreOver.segreProjectiveDimension.{u} n m) =
    Projective.ProductCoefficientMap.relativeProjectiveProductCoefficientMap S n m ≫
      (Affine.SegreOver.affineSegreStandardEmbedding (CommRingCat.of Γ(S, ⊤)) n m).left :=
  Projective.ProductCoefficientMap.projectiveSpaceProductPresentation_coefficients S n m

theorem sectionProjectiveOverMap_pair_segre {S : Scheme.{u}} (X : Over S)
    (L M : Line.Bundles.LineBundle X.left) {n m : ℕ}
    (s : Fin (n + 1) → (Line.Bundles.structureModule X.left ⟶ L.sheaf))
    (t : Fin (m + 1) → (Line.Bundles.structureModule X.left ⟶ M.sheaf))
    (hs : ∀ x : X.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ht : ∀ x : X.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (t i)) :
    lift (sectionProjectiveOverMap X s hs) (sectionProjectiveOverMap X t ht) ≫
      Projective.Products.nativeSegreProductEmbedding S n m =
    sectionProjectiveOverMap X
      (Tensor.PairSectionFrames.tensorPairSectionFamily L M (Grassmann.ProjectivePresentation.finiteProjectiveCoordinateEquiv (Segre.ChartProjections.SegreProjectiveIndex.{u} n m)) s t)
      (Tensor.PairSectionFrames.tensorPairSectionFamily_covers L M (Grassmann.ProjectivePresentation.finiteProjectiveCoordinateEquiv (Segre.ChartProjections.SegreProjectiveIndex.{u} n m)) s t hs ht) := by
  apply Over.OverMorphism.ext
  apply (RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection_isPullback S (Affine.SegreOver.segreProjectiveDimension.{u} n m)).hom_ext
  · change ((lift (sectionProjectiveOverMap X s hs) (sectionProjectiveOverMap X t ht)).left ≫
      (Projective.Products.nativeSegreProductEmbedding S n m).left) ≫ _ = _
    rw [Category.assoc, overSegre_coefficients, ← Category.assoc, overProduct_coefficients,
      ProductSegreTwisting.absoluteSectionProductMap_standardSegre]
    exact (overSection_coefficients X _ _).symm
  · exact (lift (sectionProjectiveOverMap X s hs) (sectionProjectiveOverMap X t ht) ≫
      Projective.Products.nativeSegreProductEmbedding S n m).w.trans (sectionProjectiveOverMap X _ _).w.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.OverMaps
