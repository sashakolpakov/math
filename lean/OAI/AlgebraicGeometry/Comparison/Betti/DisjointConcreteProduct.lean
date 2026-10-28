import OAI.AlgebraicGeometry.Comparison.Betti.DisjointOpenImages
import OAI.AlgebraicGeometry.Comparison.Betti.DisjointSheafSections

/-! # Disjoint Concrete Product -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.DisjointConcreteProduct

noncomputable section

section

/-! A sheaf is the product of its actual direct-image restrictions over a disjoint open cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {ι : Type} {M : ι → TopCat.{0}} {N : TopCat.{0}}
  (f : ∀ i, M i ⟶ N) (hf : ∀ i, Topology.IsOpenEmbedding (f i))

def restrictionFamily (F : ConstantSheafSections.ComplexSheaves N) (i : ι) : ConstantSheafSections.ComplexSheaves N :=
  (TopologicalSheafPullback.sheafDirectImage (f i)).obj ((Open.Image.openRestriction (f i) (hf i)).obj F)

def restrictionFanMap (F : ConstantSheafSections.ComplexSheaves N) : F ⟶ ∏ᶜ restrictionFamily f hf F :=
  Pi.lift fun i => (Open.Image.openRestrictionAdjunction (f i) (hf i)).unit.app F

abbrev openEvaluation (V : Opens N) : ConstantSheafSections.ComplexSheaves N ⥤ ModuleCat.{0} ℂ :=
  (sheafSections (Opens.grothendieckTopology N) (ModuleCat.{0} ℂ)).obj (op V)

instance openEvaluationLimits (V : Opens N) : PreservesLimits (openEvaluation V) := by
  change PreservesLimits (sheafToPresheaf (Opens.grothendieckTopology N) (ModuleCat.{0} ℂ) ⋙
    (evaluation (Opens N)ᵒᵖ (ModuleCat.{0} ℂ)).obj (op V))
  infer_instance

def evaluationProductIso (F : ConstantSheafSections.ComplexSheaves N) (V : Opens N) :
    (openEvaluation V).obj (∏ᶜ restrictionFamily f hf F) ≅
      ModuleCat.of ℂ (∀ i, F.obj.obj (op (DisjointOpenImages.openImage f hf V i))) :=
  PreservesProduct.iso (openEvaluation V) (restrictionFamily f hf F) ≪≫
    ModuleCat.piIsoPi (fun i => (openEvaluation V).obj (restrictionFamily f hf F i))

theorem evaluationProductIso_projection (F : ConstantSheafSections.ComplexSheaves N) (V : Opens N) (i : ι) :
    (evaluationProductIso f hf F V).hom ≫ ModuleCat.ofHom (LinearMap.proj i) =
      (openEvaluation V).map (Pi.π (restrictionFamily f hf F) i) := by
  let Z : ι → ModuleCat.{0} ℂ := fun j => (openEvaluation V).obj (restrictionFamily f hf F j)
  change ((PreservesProduct.iso (openEvaluation V) (restrictionFamily f hf F)).hom ≫
      (ModuleCat.piIsoPi Z).hom) ≫ ModuleCat.ofHom (LinearMap.proj i : (∀ j, Z j) →ₗ[ℂ] Z i) = _
  rw [Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype, PreservesProduct.iso_hom, piComparison_comp_π]

theorem restrictionFanMap_eval (F : ConstantSheafSections.ComplexSheaves N) (V : Opens N) :
    (openEvaluation V).map (restrictionFanMap f hf F) ≫ (evaluationProductIso f hf F V).hom =
      ModuleCat.ofHom (DisjointSheafSections.sectionRestriction (show TopCat.Sheaf (ModuleCat.{0} ℂ) N from F)
        (DisjointOpenImages.openImage f hf V) V (DisjointOpenImages.openImageInclusion f hf V)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  have h : ((openEvaluation V).map (restrictionFanMap f hf F) ≫ (evaluationProductIso f hf F V).hom) ≫
      ModuleCat.ofHom (LinearMap.proj i) =
        (openEvaluation V).map ((Open.Image.openRestrictionAdjunction (f i) (hf i)).unit.app F) := by
    erw [Category.assoc, evaluationProductIso_projection, ← (openEvaluation V).map_comp]
    change (openEvaluation V).map (Pi.lift _ ≫ Pi.π _ i) = _
    erw [Pi.lift_comp_π]
    rfl
  exact ConcreteCategory.congr_hom h x

theorem restrictionFanMap_isIso
    (hcover : ∀ y : N, ∃ i, y ∈ Set.range (f i))
    (hdisj : Pairwise (fun i j => Disjoint (Set.range (f i)) (Set.range (f j))))
    (F : ConstantSheafSections.ComplexSheaves N) : IsIso (restrictionFanMap f hf F) := by
  have hV (V : Opens N) : IsIso ((openEvaluation V).map (restrictionFanMap f hf F)) := by
    let e := evaluationProductIso f hf F V
    have h : IsIso ((openEvaluation V).map (restrictionFanMap f hf F) ≫ e.hom) := by
      change IsIso ((openEvaluation V).map (restrictionFanMap f hf F) ≫
        (evaluationProductIso f hf F V).hom)
      rw [restrictionFanMap_eval]
      change IsIso ((DisjointSheafSections.sectionEquiv (show TopCat.Sheaf (ModuleCat.{0} ℂ) N from F)
        (DisjointOpenImages.openImage f hf V) V (DisjointOpenImages.openImageInclusion f hf V)
        (DisjointOpenImages.openImage_cover f hf hcover V) (DisjointOpenImages.openImage_disjoint f hf hdisj V)).toModuleIso.hom)
      infer_instance
    exact (isIso_comp_right_iff ((openEvaluation V).map (restrictionFanMap f hf F)) e.hom).mp h
  have (V : (Opens N)ᵒᵖ) : IsIso ((restrictionFanMap f hf F).hom.app V) := hV V.unop
  have : IsIso (restrictionFanMap f hf F).hom := NatIso.isIso_of_isIso_app _
  have : IsIso ((sheafToPresheaf (Opens.grothendieckTopology N) (ModuleCat.{0} ℂ)).map
      (restrictionFanMap f hf F)) := by
    change IsIso (restrictionFanMap f hf F).hom
    infer_instance
  exact isIso_of_reflects_iso (restrictionFanMap f hf F)
    (sheafToPresheaf (Opens.grothendieckTopology N) (ModuleCat.{0} ℂ))

end

/-! Disjoint-open decomposition uses the original inverse-image adjunction units. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {ι : Type} {M : ι → TopCat.{0}} {N : TopCat.{0}}
  (f : ∀ i, M i ⟶ N) (hf : ∀ i, Topology.IsOpenEmbedding (f i))

def inverseImageFamily (F : ConstantSheafSections.ComplexSheaves N) (i : ι) : ConstantSheafSections.ComplexSheaves N :=
  (TopologicalSheafPullback.sheafDirectImage (f i)).obj ((TopologicalSheafPullback.sheafInverseImage (f i)).obj F)

def inverseImageFanMap (F : ConstantSheafSections.ComplexSheaves N) : F ⟶ ∏ᶜ inverseImageFamily f F :=
  Pi.lift fun i => (TopologicalSheafPullback.sheafImageAdjunction (f i)).unit.app F

def inverseImageRestrictionProductIso (F : ConstantSheafSections.ComplexSheaves N) :
    ∏ᶜ inverseImageFamily f F ≅ ∏ᶜ restrictionFamily f hf F :=
  Pi.mapIso fun i => (TopologicalSheafPullback.sheafDirectImage (f i)).mapIso
    ((Open.Image.openInverseImageIso (f i) (hf i)).app F)

theorem inverseImageFanMap_normalization (F : ConstantSheafSections.ComplexSheaves N) :
    inverseImageFanMap f F ≫ (inverseImageRestrictionProductIso f hf F).hom = restrictionFanMap f hf F := by
  apply Pi.hom_ext
  intro i
  change (Pi.lift _ ≫ (Pi.mapIso _).hom) ≫ Pi.π _ i = Pi.lift _ ≫ Pi.π _ i
  erw [Category.assoc, Pi.mapIso_hom_π, ← Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π]
  exact Open.Image.openInverseImageIso_unit (f i) (hf i) F

include hf in
theorem inverseImageFanMap_isIso
    (hcover : ∀ y : N, ∃ i, y ∈ Set.range (f i))
    (hdisj : Pairwise (fun i j => Disjoint (Set.range (f i)) (Set.range (f j))))
    (F : ConstantSheafSections.ComplexSheaves N) : IsIso (inverseImageFanMap f F) := by
  have : IsIso (restrictionFanMap f hf F) := restrictionFanMap_isIso f hf hcover hdisj F
  let e := inverseImageRestrictionProductIso f hf F
  have h : IsIso (inverseImageFanMap f F ≫ e.hom) := by
    change IsIso (inverseImageFanMap f F ≫ (inverseImageRestrictionProductIso f hf F).hom)
    rw [inverseImageFanMap_normalization]
    infer_instance
  exact (isIso_comp_right_iff (inverseImageFanMap f F) e.hom).mp h

end

end OAI.AlgebraicGeometry.Comparison.Betti.DisjointConcreteProduct
