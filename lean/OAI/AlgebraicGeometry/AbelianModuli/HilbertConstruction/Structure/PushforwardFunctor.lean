import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.PushforwardMorphism

/-! # Pushforward Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.PushforwardFunctor

noncomputable section

/-! Pushforward of the structure module is contravariantly functorial on schemes over a fixed base, with actual pullback-of-functions maps. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem structurePushforwardOverMorphism_id {X S : Scheme.{u}} (f : X ⟶ S) :
    PushforwardMorphism.structurePushforwardOverMorphism (𝟙 X) f f (Category.id_comp f) =
      𝟙 ((Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule X)) := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  change (PushforwardMorphism.structurePushforwardOverMorphism (𝟙 X) f f _).app U s = s
  exact (PushforwardMorphism.structurePushforwardOverMorphism_app (𝟙 X) f f (Category.id_comp f) U s).trans
    (ConcreteCategory.congr_hom
      (((𝟙 X : X ⟶ X).appLE_eq_app).trans (Scheme.Hom.id_app (f ⁻¹ᵁ U))) s)

theorem structurePushforwardOverMorphism_comp {X Y Z S : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    (ha : a ≫ g = f) (hb : b ≫ h = g) :
    PushforwardMorphism.structurePushforwardOverMorphism b g h hb ≫ PushforwardMorphism.structurePushforwardOverMorphism a f g ha =
      PushforwardMorphism.structurePushforwardOverMorphism (a ≫ b) f h
        ((Category.assoc a b h).trans ((congrArg (fun k => a ≫ k) hb).trans ha)) := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  change (PushforwardMorphism.structurePushforwardOverMorphism a f g ha).app U
    ((PushforwardMorphism.structurePushforwardOverMorphism b g h hb).app U s) =
      (PushforwardMorphism.structurePushforwardOverMorphism (a ≫ b) f h _).app U s
  have h₁ := PushforwardMorphism.structurePushforwardOverMorphism_app a f g ha U
    ((PushforwardMorphism.structurePushforwardOverMorphism b g h hb).app U s)
  have h₂ := congrArg
    (fun t : Γ(Y, g ⁻¹ᵁ U) => a.appLE (g ⁻¹ᵁ U) (f ⁻¹ᵁ U) (PushforwardMorphism.overMorphism_preimage_le a f g ha U) t)
    (PushforwardMorphism.structurePushforwardOverMorphism_app b g h hb U s)
  have h₃ := ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE a b (h ⁻¹ᵁ U)
    (g ⁻¹ᵁ U) (f ⁻¹ᵁ U) (PushforwardMorphism.overMorphism_preimage_le b g h hb U) (PushforwardMorphism.overMorphism_preimage_le a f g ha U)) s
  exact h₁.trans (h₂.trans (h₃.trans (PushforwardMorphism.structurePushforwardOverMorphism_app (a ≫ b) f h _ U s).symm))

def structurePushforwardFunctor (S : Scheme.{u}) : (Over S)ᵒᵖ ⥤ S.Modules where
  obj X := (Scheme.Modules.pushforward X.unop.hom).obj (Line.Bundles.structureModule X.unop.left)
  map a := PushforwardMorphism.structurePushforwardOverMorphism a.unop.left _ _ a.unop.w
  map_id X := structurePushforwardOverMorphism_id X.unop.hom
  map_comp a b := (structurePushforwardOverMorphism_comp b.unop.left a.unop.left
    _ _ _ b.unop.w a.unop.w).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.PushforwardFunctor
