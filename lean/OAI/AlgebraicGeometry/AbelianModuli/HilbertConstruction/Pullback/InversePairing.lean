import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorBaseChange

/-! # Inverse Pairing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.InversePairing

noncomputable section

/-! An inverse pairing of line bundles pulls back to an actual pairing, compatible with the pullback units. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (L K : Line.Bundles.LineBundle X)
variable (e : Tensor.ProductSheaf.tensorModule L.sheaf K.sheaf ≅ Line.Bundles.structureModule X)

def pullbackInversePairing : Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj L.sheaf)
    ((Scheme.Modules.pullback f).obj K.sheaf) ⟶ Line.Bundles.structureModule Y :=
  (Line.Bundles.LineBundle.tensorBaseChangeIso f L K).inv ≫ (Scheme.Modules.pullback f).map e.hom ≫
    (Line.Bundles.structureModulePullbackIso f).hom

theorem pullbackInversePairing_comparison :
    Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf K.sheaf ≫ pullbackInversePairing f L K e =
      (Scheme.Modules.pullback f).map e.hom ≫ (Line.Bundles.structureModulePullbackIso f).hom := by
  change (Line.Bundles.LineBundle.tensorBaseChangeIso f L K).hom ≫
    ((Line.Bundles.LineBundle.tensorBaseChangeIso f L K).inv ≫ _) = _
  rw [Iso.hom_inv_id_assoc]
  rfl

theorem pullbackInversePairing_unit :
    Tensor.PullbackComparison.bilinearPullbackUnit f L.sheaf K.sheaf (Line.Bundles.structureModule Y)
      (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _ (pullbackInversePairing f L K e)) =
      (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv L.sheaf K.sheaf _ e.hom).postcomp
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  have he := congrArg (fun q => Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv L.sheaf K.sheaf _
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ q))
      (pullbackInversePairing_comparison f L K e)
  rw [(Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right,
    Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp, Tensor.PullbackComparison.tensorPullbackComparison_spec,
    ← Tensor.PullbackComparison.bilinearPullbackUnit_postcomp, Tensor.Bifunctor.tensorBilinear_postcomp] at he
  rw [(Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_left] at he
  have hu : (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (Line.Bundles.structureModulePullbackIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    Tensor.PullbackUnits.structureModulePullbackIso_unit f
  rw [hu] at he
  exact he.trans (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp e.hom
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.InversePairing
