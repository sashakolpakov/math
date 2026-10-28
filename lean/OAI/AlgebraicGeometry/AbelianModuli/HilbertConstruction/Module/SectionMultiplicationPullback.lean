import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionMultiplication
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorModulePullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapCoverEquality

/-! # Section Multiplication Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionMultiplicationPullback

noncomputable section

/-! The actual multiplication map on an arbitrary module commutes with scheme pullback. Its monomorphism property can therefore be tested in affine frames on an open cover. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}}

theorem moduleSectionMultiply_pullback (f : Y ⟶ X) (L : Line.Bundles.LineBundle X) (M : X.Modules)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) :
    (Scheme.Modules.pullback f).map (SectionMultiplication.moduleSectionMultiply L M s) ≫
        Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M =
      SectionMultiplication.moduleSectionMultiply (L.pullback f) ((Scheme.Modules.pullback f).obj M) (Ample.LineBundles.pullbackSection f s) := by
  let F := Scheme.Modules.pullback f
  let E := Line.Bundles.structureModulePullbackIso f
  have hu : F.map (Tensor.ProductSheaf.tensorModuleUnitLeftIso M).inv ≫
      Tensor.PullbackComparison.tensorPullbackComparison f (Line.Bundles.structureModule X) M ≫
        Tensor.Bifunctor.tensorModuleMap E.hom (𝟙 (F.obj M)) = (Tensor.ProductSheaf.tensorModuleUnitLeftIso (F.obj M)).inv := by
    apply (cancel_mono (Tensor.ProductSheaf.tensorModuleUnitLeftIso (F.obj M)).hom).mp
    calc
      (F.map (Tensor.ProductSheaf.tensorModuleUnitLeftIso M).inv ≫
          Tensor.PullbackComparison.tensorPullbackComparison f (Line.Bundles.structureModule X) M ≫
            Tensor.Bifunctor.tensorModuleMap E.hom (𝟙 (F.obj M))) ≫ (Tensor.ProductSheaf.tensorModuleUnitLeftIso (F.obj M)).hom =
          F.map (Tensor.ProductSheaf.tensorModuleUnitLeftIso M).inv ≫ F.map (Tensor.ProductSheaf.tensorModuleUnitLeftIso M).hom := by
        simp only [E, F, Category.assoc, Tensor.PullbackLeftUnit.tensorPullbackComparison_leftUnit_formula]
      _ = 𝟙 (F.obj M) := by
        rw [← F.map_comp, Iso.inv_hom_id, F.map_id]
      _ = (Tensor.ProductSheaf.tensorModuleUnitLeftIso (F.obj M)).inv ≫ (Tensor.ProductSheaf.tensorModuleUnitLeftIso (F.obj M)).hom :=
        (Tensor.ProductSheaf.tensorModuleUnitLeftIso (F.obj M)).inv_hom_id.symm
  have hs : Tensor.Bifunctor.tensorModuleMap E.hom (𝟙 (F.obj M)) ≫
      Tensor.Bifunctor.tensorModuleMap (Ample.LineBundles.pullbackSection f s) (𝟙 (F.obj M)) =
        Tensor.Bifunctor.tensorModuleMap (F.map s) (𝟙 (F.obj M)) := by
    rw [Tensor.Bifunctor.tensorModuleMap_comp]
    simp only [E, F, Ample.LineBundles.pullbackSection, Iso.hom_inv_id_assoc, Category.id_comp]
  calc
    F.map (SectionMultiplication.moduleSectionMultiply L M s) ≫ Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M =
        F.map (Tensor.ProductSheaf.tensorModuleUnitLeftIso M).inv ≫
          Tensor.PullbackComparison.tensorPullbackComparison f (Line.Bundles.structureModule X) M ≫
            Tensor.Bifunctor.tensorModuleMap (F.map s) (𝟙 (F.obj M)) := by
      rw [SectionMultiplication.moduleSectionMultiply, F.map_comp, Category.assoc, Tensor.PullbackComparison.tensorPullbackComparison_natural,
        F.map_id]
    _ = (F.map (Tensor.ProductSheaf.tensorModuleUnitLeftIso M).inv ≫
          Tensor.PullbackComparison.tensorPullbackComparison f (Line.Bundles.structureModule X) M ≫
            Tensor.Bifunctor.tensorModuleMap E.hom (𝟙 (F.obj M))) ≫
              Tensor.Bifunctor.tensorModuleMap (Ample.LineBundles.pullbackSection f s) (𝟙 (F.obj M)) := by
      simp only [Category.assoc, hs]
    _ = SectionMultiplication.moduleSectionMultiply (L.pullback f) (F.obj M) (Ample.LineBundles.pullbackSection f s) := by
      rw [hu]
      rfl

theorem moduleSectionMultiply_pullback_mono_iff (f : Y ⟶ X) (L : Line.Bundles.LineBundle X) (M : X.Modules)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) :
    Mono ((Scheme.Modules.pullback f).map (SectionMultiplication.moduleSectionMultiply L M s)) ↔
      Mono (SectionMultiplication.moduleSectionMultiply (L.pullback f) ((Scheme.Modules.pullback f).obj M)
        (Ample.LineBundles.pullbackSection f s)) := by
  have : IsIso (Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M) :=
    LineBundle.TensorModulePullback.lineBundle_tensorModulePullbackComparison_isIso f L M
  rw [← moduleSectionMultiply_pullback f L M s]
  constructor
  · intro h
    have := h
    infer_instance
  · intro h
    have := h
    refine ⟨fun {Z} a b hab => ?_⟩
    apply (cancel_mono ((Scheme.Modules.pullback f).map (SectionMultiplication.moduleSectionMultiply L M s) ≫
      Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M)).mp
    simpa only [← Category.assoc] using
      congrArg (fun k => k ≫ Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M) hab

theorem moduleMap_mono_of_pullback_cover {M N : X.Modules} {ι : Type v}
    (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i) (f : M ⟶ N)
    (hf : ∀ i, Mono ((Scheme.Modules.pullback (U i).ι).map f)) : Mono f := by
  refine ⟨fun {Z} a b hab => ?_⟩
  apply MapCoverEquality.moduleMap_eq_of_pullback_cover U hU a b
  intro i
  let F := Scheme.Modules.pullback (U i).ι
  have : Mono (F.map f) := hf i
  apply (cancel_mono (F.map f)).mp
  rw [← F.map_comp, ← F.map_comp, hab]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionMultiplicationPullback
