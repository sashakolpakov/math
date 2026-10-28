import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.TensorCompositionUnits
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackUnits

/-! # Structure Frame Composition -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.StructureFrameComposition

noncomputable section

/-! The canonical structure-sheaf frame is coherent under composition
of scheme pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X Y Z : Scheme.{u}}

theorem structureFrame_homEquiv (f : X ⟶ Y) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
  AbelianModuli.HilbertConstruction.Tensor.PullbackUnits.structureModulePullbackIso_unit f

theorem structureFrame_pushforward_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
      (Scheme.Modules.pushforward g).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) =
      SheafOfModules.unitToPushforwardObjUnit (f ≫ g).toRingCatSheafHom := by
  ext U
  rfl

theorem structureFrame_pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.pullbackComp f g).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z) ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (f ≫ g)).hom =
      (Scheme.Modules.pullback f).map (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g).hom ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).injective
  apply (cancel_mono ((Scheme.Modules.pushforwardComp f g).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X))).mp
  rw [AbelianModuli.HilbertConstruction.Pullback.TensorCompositionUnits.pullbackComp_homEquiv, Adjunction.homEquiv_naturality_left, structureFrame_homEquiv,
    Adjunction.homEquiv_naturality_right, structureFrame_homEquiv, structureFrame_homEquiv]
  simpa only [Category.assoc] using! (structureFrame_pushforward_comp f g).symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.StructureFrameComposition
