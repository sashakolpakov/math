import OAI.AlgebraicGeometry.Comparison.Betti.DisjointConcreteProduct
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.UnitProduct
import OAI.AlgebraicGeometry.Comparison.Betti.ExactDerivedAdjunction
import OAI.AlgebraicGeometry.Comparison.Betti.Derived.ConstantPullback

/-! # Disjoint Derived Product -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.DisjointDerivedProduct

noncomputable section

/-! The actual disjoint-open unit decomposition passes through the derived localization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {ι : Type} {M : ι → TopCat.{0}} {N : TopCat.{0}} (f : ∀ i, M i ⟶ N)

def imageComposite (i : ι) : ConstantSheafSections.ComplexSheaves N ⥤ ConstantSheafSections.ComplexSheaves N :=
  TopologicalSheafPullback.sheafInverseImage (f i) ⋙ TopologicalSheafPullback.sheafDirectImage (f i)

instance imageCompositeAdditive (i : ι) : (imageComposite f i).Additive := by
  dsimp only [imageComposite]
  infer_instance

def complexInverseImageFanMap (K : CochainComplex (ConstantSheafSections.ComplexSheaves N) ℤ) :
    K ⟶ ∏ᶜ fun i => ((imageComposite f i).mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
  Complex.UnitProduct.Disjoint.complexUnitFanMap (imageComposite f) (fun i => (TopologicalSheafPullback.sheafImageAdjunction (f i)).unit) K

theorem complexInverseImageFanMap_isIso (hf : ∀ i, Topology.IsOpenEmbedding (f i))
    (hcover : ∀ y : N, ∃ i, y ∈ Set.range (f i))
    (hdisj : Pairwise (fun i j => Disjoint (Set.range (f i)) (Set.range (f j))))
    (K : CochainComplex (ConstantSheafSections.ComplexSheaves N) ℤ) : IsIso (complexInverseImageFanMap f K) :=
  Complex.UnitProduct.Disjoint.complexUnitFanMap_isIso (imageComposite f) (fun i => (TopologicalSheafPullback.sheafImageAdjunction (f i)).unit)
    (DisjointConcreteProduct.inverseImageFanMap_isIso f hf hcover hdisj) K

variable [Finite ι]

def derivedInverseImageFanMap (K : CochainComplex (ConstantSheafSections.ComplexSheaves N) ℤ) :
    DerivedCategory.Q.obj K ⟶
      ∏ᶜ fun i => DerivedCategory.Q.obj (((imageComposite f i).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  DerivedCategory.Q.map (complexInverseImageFanMap f K) ≫
    (PreservesProduct.iso DerivedCategory.Q
      (fun i => ((imageComposite f i).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).hom

theorem derivedInverseImageFanMap_projection
    (K : CochainComplex (ConstantSheafSections.ComplexSheaves N) ℤ) (i : ι) :
    derivedInverseImageFanMap f K ≫ Pi.π _ i =
      DerivedCategory.Q.map ((Complex.Adjunction.onComplexes
        (TopologicalSheafPullback.sheafImageAdjunction (f i)) (ComplexShape.up ℤ)).unit.app K) := by
  unfold derivedInverseImageFanMap
  erw [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π, ← DerivedCategory.Q.map_comp]
  change DerivedCategory.Q.map (Pi.lift _ ≫ Pi.π _ i) = _
  erw [Pi.lift_comp_π]
  rfl

theorem derivedInverseImageFanMap_isIso (hf : ∀ i, Topology.IsOpenEmbedding (f i))
    (hcover : ∀ y : N, ∃ i, y ∈ Set.range (f i))
    (hdisj : Pairwise (fun i j => Disjoint (Set.range (f i)) (Set.range (f j))))
    (K : CochainComplex (ConstantSheafSections.ComplexSheaves N) ℤ) : IsIso (derivedInverseImageFanMap f K) := by
  have : IsIso (complexInverseImageFanMap f K) := complexInverseImageFanMap_isIso f hf hcover hdisj K
  unfold derivedInverseImageFanMap
  infer_instance

end

end OAI.AlgebraicGeometry.Comparison.Betti.DisjointDerivedProduct
