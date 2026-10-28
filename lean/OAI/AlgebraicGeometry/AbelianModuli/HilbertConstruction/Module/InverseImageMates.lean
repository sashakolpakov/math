import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.InverseImageComparison
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Inverse Image Mates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.InverseImageMates

noncomputable section

/-! The module inverse-image comparison is the mate of the actual underlying-sheaf pushforward comparison. This identifies it with the canonical square to which composition laws for adjunctions apply. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {X Y : Scheme.{u}}

def moduleUnderlyingPushforwardSquare (f : X ⟶ Y) :
    TwoSquare (Scheme.Modules.pushforward f) (SheafOfModules.toSheaf X.ringCatSheaf)
      (SheafOfModules.toSheaf Y.ringCatSheaf)
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base) :=
  TwoSquare.mk _ _ _ _ (InverseImageComparison.moduleUnderlyingPushforwardIso f).hom

def moduleInverseImageSquare (f : X ⟶ Y) :
    TwoSquare (SheafOfModules.toSheaf Y.ringCatSheaf) (Scheme.Modules.pullback f)
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} f.base)
      (SheafOfModules.toSheaf X.ringCatSheaf) :=
  (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base)).symm
      (moduleUnderlyingPushforwardSquare f)

theorem moduleInverseImageSquare_app (f : X ⟶ Y) (M : Y.Modules) :
    (moduleInverseImageSquare f).app M = InverseImageComparison.moduleInverseImageComparison f M := by
  let FY : Y.Modules ⥤ Y.carrier.Sheaf AddCommGrpCat.{u} := SheafOfModules.toSheaf Y.ringCatSheaf
  let FX : X.Modules ⥤ X.carrier.Sheaf AddCommGrpCat.{u} := SheafOfModules.toSheaf X.ringCatSheaf
  let P := Scheme.Modules.pullback f
  let G := TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base
  let v : FY.obj M ⟶ G.obj (FX.obj (P.obj M)) :=
    FY.map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
      (InverseImageComparison.moduleUnderlyingPushforwardIso f).hom.app (P.obj M)
  have hl : adj.homEquiv (FY.obj M) (FX.obj (P.obj M)) ((moduleInverseImageSquare f).app M) = v := by
    calc
      _ = adj.unit.app (FY.obj M) ≫ G.map ((moduleInverseImageSquare f).app M) :=
        adj.homEquiv_unit (FY.obj M) (FX.obj (P.obj M)) ((moduleInverseImageSquare f).app M)
      _ = v := (unit_mateEquiv_symm (Scheme.Modules.pullbackPushforwardAdjunction f) adj
        (moduleUnderlyingPushforwardSquare f) M).symm
  have hr : adj.homEquiv (FY.obj M) (FX.obj (P.obj M)) (InverseImageComparison.moduleInverseImageComparison f M) = v :=
    InverseImageComparison.moduleInverseImageComparison_adjunction f M
  exact (adj.homEquiv (FY.obj M) (FX.obj (P.obj M))).injective (hl.trans hr.symm)

theorem moduleInverseImageSquare_mate (f : X ⟶ Y) :
    mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base)
      (moduleInverseImageSquare f) = moduleUnderlyingPushforwardSquare f :=
  Equiv.apply_symm_apply _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.InverseImageMates
