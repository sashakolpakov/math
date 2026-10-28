import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.PushforwardMorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeModule

/-! # Sheaf Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.SheafBaseChange

noncomputable section

/-! The base-change morphism for the structure sheaf is constructed directly from pullback of regular functions, with its adjoint and actual section values specified. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S X Y P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g)

def structureBaseChangeAdjoint :
    (Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule X) ⟶
      (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pushforward b).obj (Line.Bundles.structureModule P)) :=
  PushforwardMorphism.structurePushforwardOverMorphism a (b ≫ g) f H.w ≫
    (Scheme.Modules.pushforwardComp b g).inv.app (Line.Bundles.structureModule P)

theorem structureBaseChangeAdjoint_app (U : S.Opens) (s : Γ(X, f ⁻¹ᵁ U)) :
    (structureBaseChangeAdjoint H).app U s =
      a.appLE (f ⁻¹ᵁ U) ((b ≫ g) ⁻¹ᵁ U) (PushforwardMorphism.overMorphism_preimage_le a (b ≫ g) f H.w U) s :=
  PushforwardMorphism.structurePushforwardOverMorphism_app a (b ≫ g) f H.w U s

theorem structureBaseChangeAdjoint_appTop (s : Γ(X, ⊤)) :
    (structureBaseChangeAdjoint H).app ⊤ s = a.appTop s :=
  (structureBaseChangeAdjoint_app H ⊤ s).trans (ConcreteCategory.congr_hom a.appLE_eq_app s)

def structureBaseChangeMap :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule X)) ⟶
      (Scheme.Modules.pushforward b).obj (Line.Bundles.structureModule P) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm (structureBaseChangeAdjoint H)

theorem structureBaseChangeMap_normalization :
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _ (structureBaseChangeMap H) =
      structureBaseChangeAdjoint H :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).apply_symm_apply _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.SheafBaseChange
