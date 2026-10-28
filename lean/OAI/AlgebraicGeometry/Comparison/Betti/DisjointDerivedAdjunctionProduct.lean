import OAI.AlgebraicGeometry.Comparison.Betti.DisjointDerivedProduct
import OAI.AlgebraicGeometry.Comparison.Betti.Closed.DerivedImage

/-! # Disjoint Derived Adjunction Product -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.DisjointDerivedAdjunctionProduct

noncomputable section

/-! The genuine derived adjunction units decompose objects over a finite clopen partition. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {ι : Type} [Finite ι] {M : ι → TopCat.{0}} {N : TopCat.{0}}
  (f : ∀ i, M i ⟶ N) (hf : ∀ i, Topology.IsOpenEmbedding (f i))
  (hc : ∀ i, IsClosed (Set.range (f i)))

def derivedImageComposite (i : ι) :
    DerivedCategory (ConstantSheafSections.ComplexSheaves N) ⥤ DerivedCategory (ConstantSheafSections.ComplexSheaves N) :=
  (TopologicalSheafPullback.sheafInverseImage (f i)).mapDerivedCategory ⋙
    Closed.DerivedImage.closedDerivedDirectImage (f i) (hf i).isInducing (hc i)

def derivedComplexImageIso (K : CochainComplex (ConstantSheafSections.ComplexSheaves N) ℤ) (i : ι) :
    DerivedCategory.Q.obj (((DisjointDerivedProduct.imageComposite f i).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      (derivedImageComposite f hf hc i).obj (DerivedCategory.Q.obj K) :=
  ((Closed.DerivedImage.closedDerivedDirectImageFactors (f i) (hf i).isInducing (hc i)).app
    (((TopologicalSheafPullback.sheafInverseImage (f i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).symm ≪≫
    (Closed.DerivedImage.closedDerivedDirectImage (f i) (hf i).isInducing (hc i)).mapIso
      (((TopologicalSheafPullback.sheafInverseImage (f i)).mapDerivedCategoryFactors).app K).symm

def derivedAdjunctionFanMap (A : DerivedCategory (ConstantSheafSections.ComplexSheaves N)) :
    A ⟶ ∏ᶜ fun i => (derivedImageComposite f hf hc i).obj A :=
  Pi.lift fun i => (Closed.DerivedImage.closedDerivedImageAdjunction (f i) (hf i).isInducing (hc i)).unit.app A

theorem derivedAdjunctionFanMap_projection (A : DerivedCategory (ConstantSheafSections.ComplexSheaves N)) (i : ι) :
    derivedAdjunctionFanMap f hf hc A ≫ Pi.π _ i =
      (Closed.DerivedImage.closedDerivedImageAdjunction (f i) (hf i).isInducing (hc i)).unit.app A :=
  Pi.lift_comp_π _ i

theorem derivedAdjunctionFanMap_normalization (K : CochainComplex (ConstantSheafSections.ComplexSheaves N) ℤ) :
    derivedAdjunctionFanMap f hf hc (DerivedCategory.Q.obj K) =
      DisjointDerivedProduct.derivedInverseImageFanMap f K ≫ (Pi.mapIso (derivedComplexImageIso f hf hc K)).hom := by
  apply Pi.hom_ext
  intro i
  change Pi.lift _ ≫ Pi.π _ i = _
  erw [Pi.lift_comp_π, Category.assoc, Pi.mapIso_hom_π, ← Category.assoc,
    DisjointDerivedProduct.derivedInverseImageFanMap_projection]
  exact Closed.DerivedImage.closedDerivedImageAdjunction_unit (f i) (hf i).isInducing (hc i) K

theorem derivedAdjunctionFanMap_isIso_Q
    (hcover : ∀ y : N, ∃ i, y ∈ Set.range (f i))
    (hdisj : Pairwise (fun i j => Disjoint (Set.range (f i)) (Set.range (f j))))
    (K : CochainComplex (ConstantSheafSections.ComplexSheaves N) ℤ) :
    IsIso (derivedAdjunctionFanMap f hf hc (DerivedCategory.Q.obj K)) := by
  have : IsIso (DisjointDerivedProduct.derivedInverseImageFanMap f K) := DisjointDerivedProduct.derivedInverseImageFanMap_isIso f hf hcover hdisj K
  rw [derivedAdjunctionFanMap_normalization]
  infer_instance

theorem derivedAdjunctionFanMap_naturality
    {A B : DerivedCategory (ConstantSheafSections.ComplexSheaves N)} (a : A ⟶ B) :
    a ≫ derivedAdjunctionFanMap f hf hc B = derivedAdjunctionFanMap f hf hc A ≫
      CategoryTheory.Limits.Pi.map (fun i => (derivedImageComposite f hf hc i).map a) := by
  apply Pi.hom_ext
  intro i
  erw [Category.assoc, Category.assoc, Pi.map_π,
    ← Category.assoc (derivedAdjunctionFanMap f hf hc A),
    derivedAdjunctionFanMap_projection, derivedAdjunctionFanMap_projection]
  exact (Closed.DerivedImage.closedDerivedImageAdjunction (f i) (hf i).isInducing (hc i)).unit.naturality a

theorem derivedAdjunctionFanMap_isIso
    (hcover : ∀ y : N, ∃ i, y ∈ Set.range (f i))
    (hdisj : Pairwise (fun i j => Disjoint (Set.range (f i)) (Set.range (f j))))
    (A : DerivedCategory (ConstantSheafSections.ComplexSheaves N)) : IsIso (derivedAdjunctionFanMap f hf hc A) := by
  let Q : CochainComplex (ConstantSheafSections.ComplexSheaves N) ℤ ⥤ DerivedCategory (ConstantSheafSections.ComplexSheaves N) :=
    DerivedCategory.Q
  let K := Q.objPreimage A
  let e := Q.objObjPreimageIso A
  have : IsIso (derivedAdjunctionFanMap f hf hc (Q.obj K)) :=
    derivedAdjunctionFanMap_isIso_Q f hf hc hcover hdisj K
  have h : IsIso (e.hom ≫ derivedAdjunctionFanMap f hf hc A) := by
    rw [derivedAdjunctionFanMap_naturality]
    infer_instance
  exact (isIso_comp_left_iff e.hom (derivedAdjunctionFanMap f hf hc A)).mp h

end

end OAI.AlgebraicGeometry.Comparison.Betti.DisjointDerivedAdjunctionProduct
