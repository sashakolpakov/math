import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.InversePairing

/-! # Traced Inverse Pairing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TracedInversePairing

noncomputable section

/-! A structure-sheaf trace turns the pulled-back inverse pairing into a pairing that retracts the original line-bundle pairing. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (L K : Line.Bundles.LineBundle X)
variable (e : Tensor.ProductSheaf.tensorModule L.sheaf K.sheaf ≅ Line.Bundles.structureModule X)
variable (t : (Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule Y) ⟶ Line.Bundles.structureModule X)

def tracedInversePairing : Tensor.ProductSheaf.tensorModule
    ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj L.sheaf)) K.sheaf ⟶
      Line.Bundles.structureModule X :=
  (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).symm
    ((((Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _ (Pullback.InversePairing.pullbackInversePairing f L K e)).pushforward f).precomp
      (𝟙 _) ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app K.sheaf)).postcomp t)

theorem tracedInversePairing_unit
    (ht : SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫ t = 𝟙 _) :
    Tensor.Bifunctor.tensorModuleMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf) (𝟙 K.sheaf) ≫
      tracedInversePairing f L K e t = e.hom := by
  apply (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv L.sheaf K.sheaf _).injective
  let η : L.sheaf ⟶ (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj L.sheaf) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf
  refine (Tensor.PullbackComparison.tensorHomEquiv_precomp η (𝟙 K.sheaf) (tracedInversePairing f L K e t)).trans ?_
  rw [tracedInversePairing, Equiv.apply_symm_apply,
    Bilinear.Sheaves.SheafBilinearMap.precomp_postcomp, Bilinear.Sheaves.SheafBilinearMap.precomp_comp,
    Category.comp_id, Category.id_comp]
  change (Tensor.PullbackComparison.bilinearPullbackUnit f L.sheaf K.sheaf (Line.Bundles.structureModule Y)
    (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _ (Pullback.InversePairing.pullbackInversePairing f L K e))).postcomp t = _
  rw [Pullback.InversePairing.pullbackInversePairing_unit]
  let β := Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv L.sheaf K.sheaf (Line.Bundles.structureModule X) e.hom
  exact (β.postcomp_comp (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) t).symm.trans
    ((congrArg β.postcomp ht).trans β.postcomp_id)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TracedInversePairing
