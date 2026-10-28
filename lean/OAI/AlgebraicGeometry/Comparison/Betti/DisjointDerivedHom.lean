import OAI.AlgebraicGeometry.Comparison.Betti.DisjointDerivedAdjunctionProduct
import OAI.AlgebraicGeometry.Comparison.Betti.ProductHomEquiv

/-! # Disjoint Derived Hom -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.DisjointDerivedHom

noncomputable section

section

/-! The derived decomposition identifies morphisms with their actual inverse images. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {ι : Type} [Finite ι] {M : ι → TopCat.{0}} {N : TopCat.{0}}
  (f : ∀ i, M i ⟶ N) (hf : ∀ i, Topology.IsOpenEmbedding (f i))
  (hc : ∀ i, IsClosed (Set.range (f i)))
  (hcover : ∀ y : N, ∃ i, y ∈ Set.range (f i))
  (hdisj : Pairwise (fun i j => Disjoint (Set.range (f i)) (Set.range (f j))))

def derivedHomEquiv (A B : DerivedCategory (ConstantSheafSections.ComplexSheaves N)) :
    (A ⟶ B) ≃ₗ[ℂ]
      (∀ i, (TopologicalSheafPullback.sheafInverseImage (f i)).mapDerivedCategory.obj A ⟶
        (TopologicalSheafPullback.sheafInverseImage (f i)).mapDerivedCategory.obj B) := by
  have : IsIso (DisjointDerivedAdjunctionProduct.derivedAdjunctionFanMap f hf hc B) := DisjointDerivedAdjunctionProduct.derivedAdjunctionFanMap_isIso f hf hc hcover hdisj B
  exact (Linear.homCongr ℂ (Iso.refl A) (asIso (DisjointDerivedAdjunctionProduct.derivedAdjunctionFanMap f hf hc B))).trans
    ((ProductHomEquiv.Disjoint.homProductLinearEquiv (R := ℂ) A (fun i => (DisjointDerivedAdjunctionProduct.derivedImageComposite f hf hc i).obj B)).trans
      (LinearEquiv.piCongrRight fun i =>
        (Closed.DerivedImage.closedDerivedImageHomLinearEquiv (f i) (hf i).isInducing (hc i) A
          ((TopologicalSheafPullback.sheafInverseImage (f i)).mapDerivedCategory.obj B)).symm))

theorem derivedHomEquiv_apply (A B : DerivedCategory (ConstantSheafSections.ComplexSheaves N)) (a : A ⟶ B) (i : ι) :
    derivedHomEquiv f hf hc hcover hdisj A B a i =
      (TopologicalSheafPullback.sheafInverseImage (f i)).mapDerivedCategory.map a := by
  let adj := Closed.DerivedImage.closedDerivedImageAdjunction (f i) (hf i).isInducing (hc i)
  let F := (TopologicalSheafPullback.sheafInverseImage (f i)).mapDerivedCategory
  change (adj.homEquiv A (F.obj B)).symm
      (((𝟙 A ≫ a) ≫ DisjointDerivedAdjunctionProduct.derivedAdjunctionFanMap f hf hc B) ≫ Pi.π _ i) = F.map a
  erw [Category.id_comp, Category.assoc, DisjointDerivedAdjunctionProduct.derivedAdjunctionFanMap_projection]
  apply (adj.homEquiv A (F.obj B)).injective
  rw [Equiv.apply_symm_apply]
  exact (ProductHomEquiv.Disjoint.homEquiv_map adj a).symm

end

/-! Genuine sheaf hypercohomology decomposes by the original inverse-image restriction maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

abbrev complexHypercohomology (M : TopCat.{0}) (K : CochainComplex (ConstantSheafSections.ComplexSheaves M) ℤ) (n : ℤ) :=
  ShiftedHom ((DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves M) 0).obj
    (ConstantSheafSections.standardConstantSheaf M)) (DerivedCategory.Q.obj K) n

section Restriction

variable {M N : TopCat.{0}} (f : M ⟶ N) (K : CochainComplex (ConstantSheafSections.ComplexSheaves N) ℤ) (n : ℤ)

def hypercohomologyCoefficientIso :
    (TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategory.obj ((DerivedCategory.Q.obj K)⟦n⟧) ≅
      (DerivedCategory.Q.obj
        (((TopologicalSheafPullback.sheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))⟦n⟧ :=
  (((TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategory.commShiftIso n).app (DerivedCategory.Q.obj K)) ≪≫
    (shiftFunctor (DerivedCategory (ConstantSheafSections.ComplexSheaves M)) n).mapIso
      ((TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategoryFactors.app K)

def inverseImageHypercohomologyEquiv :
    ((TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves N) 0).obj (ConstantSheafSections.standardConstantSheaf N)) ⟶
      (TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategory.obj ((DerivedCategory.Q.obj K)⟦n⟧)) ≃ₗ[ℂ]
    complexHypercohomology M (((TopologicalSheafPullback.sheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n :=
  Linear.homCongr ℂ (Derived.ConstantPullback.derivedConstantPullbackIso f) (hypercohomologyCoefficientIso f K n)

def inverseImageHypercohomologyMap : complexHypercohomology N K n →ₗ[ℂ]
    complexHypercohomology M (((TopologicalSheafPullback.sheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n where
  toFun a := (Derived.ConstantPullback.derivedConstantPullbackIso f).inv ≫
    ShiftedHom.map a (TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategory ≫
      ((TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategoryFactors.hom.app K)⟦n⟧'
  map_add' a b := by
    simp only [ShiftedHom.map, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
  map_smul' c a := by
    simp only [ShiftedHom.map, Functor.map_smul, Linear.comp_smul, Linear.smul_comp, RingHom.id_apply]

theorem inverseImageHypercohomologyEquiv_map (a : complexHypercohomology N K n) :
    inverseImageHypercohomologyEquiv f K n ((TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategory.map a) =
      inverseImageHypercohomologyMap f K n a := by
  change ((Derived.ConstantPullback.derivedConstantPullbackIso f).inv ≫
      (TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategory.map a) ≫
      ((((TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategory.commShiftIso n).hom.app (DerivedCategory.Q.obj K)) ≫
        ((TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategoryFactors.hom.app K)⟦n⟧') = _
  simp only [inverseImageHypercohomologyMap, LinearMap.coe_mk, AddHom.coe_mk,
    ShiftedHom.map, Category.assoc]

end Restriction

variable {ι : Type} [Finite ι] {M : ι → TopCat.{0}} {N : TopCat.{0}}
  (f : ∀ i, M i ⟶ N) (hf : ∀ i, Topology.IsOpenEmbedding (f i))
  (hc : ∀ i, IsClosed (Set.range (f i)))
  (hcover : ∀ y : N, ∃ i, y ∈ Set.range (f i))
  (hdisj : Pairwise (fun i j => Disjoint (Set.range (f i)) (Set.range (f j))))

def hypercohomologyEquiv (K : CochainComplex (ConstantSheafSections.ComplexSheaves N) ℤ) (n : ℤ) :
    complexHypercohomology N K n ≃ₗ[ℂ]
      (∀ i, complexHypercohomology (M i)
        (((TopologicalSheafPullback.sheafInverseImage (f i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n) :=
  (derivedHomEquiv f hf hc hcover hdisj _ _).trans
    (LinearEquiv.piCongrRight fun i => inverseImageHypercohomologyEquiv (f i) K n)

theorem hypercohomologyEquiv_apply (K : CochainComplex (ConstantSheafSections.ComplexSheaves N) ℤ)
    (n : ℤ) (a : complexHypercohomology N K n) (i : ι) :
    hypercohomologyEquiv f hf hc hcover hdisj K n a i = inverseImageHypercohomologyMap (f i) K n a := by
  change inverseImageHypercohomologyEquiv (f i) K n (derivedHomEquiv f hf hc hcover hdisj _ _ a i) = _
  rw [derivedHomEquiv_apply]
  exact inverseImageHypercohomologyEquiv_map (f i) K n a

end

end OAI.AlgebraicGeometry.Comparison.Betti.DisjointDerivedHom
