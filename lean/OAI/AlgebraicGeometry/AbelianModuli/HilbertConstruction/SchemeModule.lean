import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Scheme Module -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeModule.SchemeModuleBaseChange

noncomputable section

/-! An actual Cartesian scheme square gives the canonical base-change morphism between actual module-sheaf inverse and direct images. No invertibility assertion is assumed. -/
open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.AlgebraicGeometry
universe u
variable {S X Y P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g)

def pushforwardSquareIso :
    Scheme.Modules.pushforward a ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward b ⋙ Scheme.Modules.pushforward g :=
  Scheme.Modules.pushforwardComp a f ≪≫ Scheme.Modules.pushforwardCongr H.w ≪≫
    (Scheme.Modules.pushforwardComp b g).symm

def map : Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback g ⟶
    Scheme.Modules.pullback a ⋙ Scheme.Modules.pushforward b :=
  ((mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction a)
    (Scheme.Modules.pullbackPushforwardAdjunction g)).symm
      (TwoSquare.mk _ _ _ _ (pushforwardSquareIso H).hom)).natTrans

theorem map_app (M : X.Modules) :
    (SchemeModuleBaseChange.map H).app M =
      (Scheme.Modules.pullback g).map
        ((Scheme.Modules.pushforward f).map
          ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M)) ≫
      (Scheme.Modules.pullback g).map
        ((pushforwardSquareIso H).hom.app ((Scheme.Modules.pullback a).obj M)) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction g).counit.app
        ((Scheme.Modules.pushforward b).obj ((Scheme.Modules.pullback a).obj M)) := by
  dsimp [SchemeModuleBaseChange.map, mateEquiv]
  simp only [Category.id_comp, Category.comp_id]
  erw [(Scheme.Modules.pullback g).map_id, (Scheme.Modules.pullback g).map_id,
    Category.id_comp]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeModule.SchemeModuleBaseChange
