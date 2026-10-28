import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionMultiplication
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionTensor

/-! # Frame Tensor Natural Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.FrameTensorNaturalIso

noncomputable section

/-! A global frame trivializes tensoring by a line bundle naturally in
the coefficient module. Under this natural isomorphism, tensoring by a
section becomes multiplication by its actual frame coordinate. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}}

theorem moduleSectionFrameIso_natural (L : Line.Bundles.LineBundle X) (e : L.sheaf ≅ Line.Bundles.structureModule X)
    {M N : X.Modules} (f : M ⟶ N) :
    Tensor.Bifunctor.tensorModuleMap (𝟙 L.sheaf) f ≫ (Module.SectionMultiplication.moduleSectionFrameIso L N e).hom =
      (Module.SectionMultiplication.moduleSectionFrameIso L M e).hom ≫ f := by
  change Tensor.Bifunctor.tensorModuleMap (𝟙 L.sheaf) f ≫
      (Tensor.Bifunctor.tensorModuleMap e.hom (𝟙 N) ≫ (Tensor.ProductSheaf.tensorModuleUnitLeftIso N).hom) =
    (Tensor.Bifunctor.tensorModuleMap e.hom (𝟙 M) ≫ (Tensor.ProductSheaf.tensorModuleUnitLeftIso M).hom) ≫ f
  calc
    _ = (Tensor.Bifunctor.tensorModuleMap e.hom (𝟙 M) ≫ Tensor.Bifunctor.tensorModuleMap (𝟙 (Line.Bundles.structureModule X)) f) ≫
        (Tensor.ProductSheaf.tensorModuleUnitLeftIso N).hom := by
      rw [← Category.assoc, Tensor.Bifunctor.tensorModuleMap_comp, Tensor.Bifunctor.tensorModuleMap_comp]
      simp only [Category.id_comp, Category.comp_id]
    _ = _ := by rw [Category.assoc, Tensor.UnitLeftNaturality.tensorModuleUnitLeftIso_hom_natural, ← Category.assoc]

def lineBundleFrameTensorIso (L : Line.Bundles.LineBundle X) (e : L.sheaf ≅ Line.Bundles.structureModule X) :
    (TensorEquivalence.lineBundleTensorEquivalence L).functor ≅ 𝟭 X.Modules :=
  NatIso.ofComponents (fun M => TensorEquivalence.lineBundleTensorEquivalence_objIso L M ≪≫ Module.SectionMultiplication.moduleSectionFrameIso L M e) (by
    intro M N f
    change (TensorEquivalence.lineBundleTensorEquivalence L).functor.map f ≫
        ((TensorEquivalence.lineBundleTensorEquivalence_objIso L N).hom ≫ (Module.SectionMultiplication.moduleSectionFrameIso L N e).hom) =
      ((TensorEquivalence.lineBundleTensorEquivalence_objIso L M).hom ≫ (Module.SectionMultiplication.moduleSectionFrameIso L M e).hom) ≫ f
    rw [← Category.assoc, SectionTensor.lineBundleTensorEquivalence_objIso_natural, Category.assoc,
      moduleSectionFrameIso_natural, ← Category.assoc])

theorem lineBundleSectionTensorMap_frame (L : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (e : L.sheaf ≅ Line.Bundles.structureModule X) (M : X.Modules) :
    SectionTensor.lineBundleSectionTensorMap L s M ≫ (lineBundleFrameTensorIso L e).hom.app M =
      Global.ModuleScalars.globalModuleScalar M (Frame.Coordinates.structureModuleEndValue X (s ≫ e.hom)) := by
  calc
    _ = Module.SectionMultiplication.moduleSectionMultiply L M s ≫ (Module.SectionMultiplication.moduleSectionFrameIso L M e).hom := by
      change ((Tensor.ProductSheaf.tensorModuleUnitLeftIso M).inv ≫ Tensor.Bifunctor.tensorModuleMap s (𝟙 M) ≫
          (TensorEquivalence.lineBundleTensorEquivalence_objIso L M).inv) ≫
        ((TensorEquivalence.lineBundleTensorEquivalence_objIso L M).hom ≫ (Module.SectionMultiplication.moduleSectionFrameIso L M e).hom) = _
      simp only [Module.SectionMultiplication.moduleSectionMultiply, Category.assoc, Iso.inv_hom_id_assoc]
    _ = _ := Module.SectionMultiplication.moduleSectionMultiply_frame L M s e

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.FrameTensorNaturalIso
