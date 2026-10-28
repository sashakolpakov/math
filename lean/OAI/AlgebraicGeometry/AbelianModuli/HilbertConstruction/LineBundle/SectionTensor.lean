import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.UnitLeftNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorPullbackFunctor

/-! # Section Tensor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionTensor

noncomputable section

/-! An actual line-bundle section tensors every module naturally, and this map is invertible after any pullback on which the section becomes a frame. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {X Y : Scheme.{u}}

theorem lineBundleTensorEquivalence_objIso_natural (L : Line.Bundles.LineBundle X)
    {M N : X.Modules} (f : M ⟶ N) :
    (TensorEquivalence.lineBundleTensorEquivalence L).functor.map f ≫ (TensorEquivalence.lineBundleTensorEquivalence_objIso L N).hom =
      (TensorEquivalence.lineBundleTensorEquivalence_objIso L M).hom ≫ Tensor.Bifunctor.tensorModuleMap (𝟙 L.sheaf) f :=
  Module.MonoidalTensorRightNaturality.moduleMonoidalTensorIso_natural_right L.sheaf f

def lineBundleSectionTensorMap (L : Line.Bundles.LineBundle X) (s : Line.Bundles.structureModule X ⟶ L.sheaf)
    (M : X.Modules) : M ⟶ (TensorEquivalence.lineBundleTensorEquivalence L).functor.obj M :=
  (Tensor.ProductSheaf.tensorModuleUnitLeftIso M).inv ≫ Tensor.Bifunctor.tensorModuleMap s (𝟙 M) ≫
    (TensorEquivalence.lineBundleTensorEquivalence_objIso L M).inv

theorem lineBundleSectionTensorMap_natural (L : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) {M N : X.Modules} (f : M ⟶ N) :
    f ≫ lineBundleSectionTensorMap L s N =
      lineBundleSectionTensorMap L s M ≫ (TensorEquivalence.lineBundleTensorEquivalence L).functor.map f := by
  apply (cancel_mono (TensorEquivalence.lineBundleTensorEquivalence_objIso L N).hom).mp
  calc
    (f ≫ lineBundleSectionTensorMap L s N) ≫ (TensorEquivalence.lineBundleTensorEquivalence_objIso L N).hom =
        f ≫ (Tensor.ProductSheaf.tensorModuleUnitLeftIso N).inv ≫ Tensor.Bifunctor.tensorModuleMap s (𝟙 N) := by
      simp only [lineBundleSectionTensorMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = (Tensor.ProductSheaf.tensorModuleUnitLeftIso M).inv ≫ Tensor.Bifunctor.tensorModuleMap (𝟙 (Line.Bundles.structureModule X)) f ≫
        Tensor.Bifunctor.tensorModuleMap s (𝟙 N) := by
      rw [← Category.assoc, Tensor.UnitLeftNaturality.tensorModuleUnitLeftIso_inv_natural, Category.assoc]
    _ = (Tensor.ProductSheaf.tensorModuleUnitLeftIso M).inv ≫ Tensor.Bifunctor.tensorModuleMap s (𝟙 M) ≫
        Tensor.Bifunctor.tensorModuleMap (𝟙 L.sheaf) f := by
      rw [Tensor.Bifunctor.tensorModuleMap_comp, Tensor.Bifunctor.tensorModuleMap_comp]
      simp only [Category.id_comp, Category.comp_id]
    _ = (lineBundleSectionTensorMap L s M ≫ (TensorEquivalence.lineBundleTensorEquivalence L).functor.map f) ≫
        (TensorEquivalence.lineBundleTensorEquivalence_objIso L N).hom := by
      rw [Category.assoc, lineBundleTensorEquivalence_objIso_natural]
      simp only [lineBundleSectionTensorMap, Category.assoc, Iso.inv_hom_id_assoc]

def lineBundleSectionTensor (L : Line.Bundles.LineBundle X) (s : Line.Bundles.structureModule X ⟶ L.sheaf) :
    𝟭 X.Modules ⟶ (TensorEquivalence.lineBundleTensorEquivalence L).functor where
  app := lineBundleSectionTensorMap L s
  naturality _ _ f := lineBundleSectionTensorMap_natural L s f

theorem lineBundleSectionTensorMap_isIso (L : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) [IsIso s] (M : X.Modules) :
    IsIso (lineBundleSectionTensorMap L s M) := by
  unfold lineBundleSectionTensorMap
  infer_instance

theorem lineBundleSectionTensorMap_pullback_isIso (L : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (f : Y ⟶ X)
    [IsIso ((Scheme.Modules.pullback f).map s)] (M : X.Modules) :
    IsIso ((Scheme.Modules.pullback f).map (lineBundleSectionTensorMap L s M)) := by
  let P := Scheme.Modules.pullback f
  have : IsIso (Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M) :=
    TensorModulePullback.lineBundle_tensorModulePullbackComparison_isIso f L M
  have : IsIso (Tensor.PullbackComparison.tensorPullbackComparison f (Line.Bundles.structureModule X) M) :=
    Tensor.PullbackLeftUnit.tensorPullbackComparison_leftUnit_isIso f M
  have hc : IsIso (P.map (Tensor.Bifunctor.tensorModuleMap s (𝟙 M)) ≫ Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M) := by
    rw [Tensor.PullbackComparison.tensorPullbackComparison_natural]
    infer_instance
  have : IsIso (P.map (Tensor.Bifunctor.tensorModuleMap s (𝟙 M))) := (isIso_comp_right_iff _ _).mp hc
  change IsIso (P.map (lineBundleSectionTensorMap L s M))
  unfold lineBundleSectionTensorMap
  rw [P.map_comp, P.map_comp]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionTensor
