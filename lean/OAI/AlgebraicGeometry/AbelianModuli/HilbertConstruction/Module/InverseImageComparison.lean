import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.SheafInverseImage
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Inverse Image Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.InverseImageComparison

noncomputable section

/-! The underlying abelian sheaf of module pullback receives the canonical inverse-image map. This map is the adjoint of the actual module adjunction unit. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {X Y : Scheme.{u}}

def moduleUnderlyingPushforwardIso (f : X ⟶ Y) :
    Scheme.Modules.pushforward f ⋙ SheafOfModules.toSheaf Y.ringCatSheaf ≅
      SheafOfModules.toSheaf X.ringCatSheaf ⋙
        TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

def moduleInverseImageComparison (f : X ⟶ Y) (M : Y.Modules) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} f.base).obj
        ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M) ⟶
      (SheafOfModules.toSheaf X.ringCatSheaf).obj ((Scheme.Modules.pullback f).obj M) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base).homEquiv _ _).symm
    ((SheafOfModules.toSheaf Y.ringCatSheaf).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
        (moduleUnderlyingPushforwardIso f).hom.app ((Scheme.Modules.pullback f).obj M))

theorem moduleInverseImageComparison_adjunction (f : X ⟶ Y) (M : Y.Modules) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base).homEquiv _ _
      (moduleInverseImageComparison f M) =
        (SheafOfModules.toSheaf Y.ringCatSheaf).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
            (moduleUnderlyingPushforwardIso f).hom.app ((Scheme.Modules.pullback f).obj M) :=
  Equiv.apply_symm_apply _ _

theorem moduleInverseImageComparison_naturality (f : X ⟶ Y)
    {M N : Y.Modules} (a : M ⟶ N) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} f.base).map
        ((SheafOfModules.toSheaf Y.ringCatSheaf).map a) ≫
      moduleInverseImageComparison f N =
    moduleInverseImageComparison f M ≫
      (SheafOfModules.toSheaf X.ringCatSheaf).map ((Scheme.Modules.pullback f).map a) := by
  let FY : Y.Modules ⥤ Y.carrier.Sheaf AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf Y.ringCatSheaf
  let FX : X.Modules ⥤ X.carrier.Sheaf AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf X.ringCatSheaf
  let P := Scheme.Modules.pullback f
  let Q := Scheme.Modules.pushforward f
  let G := TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base
  let σ : Q ⋙ FY ≅ FX ⋙ G := moduleUnderlyingPushforwardIso f
  let uM : M ⟶ Q.obj (P.obj M) := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M
  let uN : N ⟶ Q.obj (P.obj N) := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N
  let vM : FY.obj M ⟶ G.obj (FX.obj (P.obj M)) := FY.map uM ≫ σ.hom.app (P.obj M)
  let vN : FY.obj N ⟶ G.obj (FX.obj (P.obj N)) := FY.map uN ≫ σ.hom.app (P.obj N)
  have hu : a ≫ uN = uM ≫ Q.map (P.map a) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality a
  have hn : FY.map a ≫ FY.map uN = FY.map uM ≫ FY.map (Q.map (P.map a)) :=
    (FY.map_comp a uN).symm.trans
      ((congrArg (fun z : M ⟶ Q.obj (P.obj N) => FY.map z) hu).trans
        (FY.map_comp uM (Q.map (P.map a))))
  have hs : FY.map (Q.map (P.map a)) ≫ σ.hom.app (P.obj N) =
      σ.hom.app (P.obj M) ≫ G.map (FX.map (P.map a)) := σ.hom.naturality (P.map a)
  have hv : FY.map a ≫ vN = vM ≫ G.map (FX.map (P.map a)) := by
    change FY.map a ≫ (FY.map uN ≫ σ.hom.app (P.obj N)) =
      (FY.map uM ≫ σ.hom.app (P.obj M)) ≫ G.map (FX.map (P.map a))
    rw [← Category.assoc, hn, Category.assoc, hs, ← Category.assoc]
  exact Adjunction.homEquiv_naturality_right_square
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base)
    (FY.map a) vN vM (FX.map (P.map a)) hv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.InverseImageComparison
