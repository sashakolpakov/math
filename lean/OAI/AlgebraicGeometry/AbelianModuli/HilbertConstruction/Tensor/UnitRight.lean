import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackUnits

/-! # Unit Right -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.UnitRight

noncomputable section

/-! The right tensor-unit isomorphism of actual module sheaves, with its explicit scalar formula on sections. -/
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry
universe u

variable {X : Scheme.{u}}
local instance (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

def tensorModuleUnitRightIso (M : X.Modules) : ProductSheaf.tensorModule M (Line.Bundles.structureModule X) ≅ M := by
  have : IsIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit := inferInstance
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (ρ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).app M

def unitRightBilinear (M : X.Modules) : Bilinear.Sheaves.SheafBilinearMap M (Line.Bundles.structureModule X) M where
  app U := (LinearMap.lsmul Γ(X, U) Γ(M, U)).flip
  naturality h m r := M.val.map_smul h.op r m

theorem tensorModuleUnitRightIso_formula (M : X.Modules) :
    Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M (Line.Bundles.structureModule X) M
      (tensorModuleUnitRightIso M).hom = unitRightBilinear M := by
  let a : PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf)
      M.val (Line.Bundles.structureModule X).val ⟶ M.val := (ρ_ M.val).hom
  have h : ProductSheaf.tensorModuleHomEquiv M (Line.Bundles.structureModule X) M
      (tensorModuleUnitRightIso M).hom = a :=
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ M).apply_symm_apply a
  change Bilinear.Sheaves.SheafBilinearMap.ofTensorPresheafHom
    (ProductSheaf.tensorModuleHomEquiv M (Line.Bundles.structureModule X) M (tensorModuleUnitRightIso M).hom) = _
  rw [h]
  ext U
  rfl

theorem tensorModuleUnitRightIso_pairing (M : X.Modules) (U : X.Opens)
    (m : Γ(M, U)) (r : Γ(X, U)) :
    (tensorModuleUnitRightIso M).hom.app U ((Bifunctor.tensorBilinear M (Line.Bundles.structureModule X)).app U m r) =
      r • m := by
  have h := (Bifunctor.tensorBilinear_postcomp (tensorModuleUnitRightIso M).hom).trans
    (tensorModuleUnitRightIso_formula M)
  exact congrArg (fun β : Bilinear.Sheaves.SheafBilinearMap M (Line.Bundles.structureModule X) M => β.app U m r) h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.UnitRight
