import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Pushforward Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.PushforwardMorphism

noncomputable section

/-! A morphism of total spaces induces the actual pullback-of-functions morphism between their pushed-forward structure modules. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X Y S : Scheme.{u}}

def structurePushforwardMorphism (a : X ⟶ Y) (g : Y ⟶ S) :
    (Scheme.Modules.pushforward g).obj (Line.Bundles.structureModule Y) ⟶
      (Scheme.Modules.pushforward (a ≫ g)).obj (Line.Bundles.structureModule X) :=
  (Scheme.Modules.pushforward g).map (SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp a g).hom.app (Line.Bundles.structureModule X)

theorem structurePushforwardMorphism_app (a : X ⟶ Y) (g : Y ⟶ S) (U : S.Opens)
    (s : Γ(Y, g ⁻¹ᵁ U)) :
    (structurePushforwardMorphism a g).app U s = a.app (g ⁻¹ᵁ U) s := rfl

def structurePushforwardOverMorphism (a : X ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S)
    (ha : a ≫ g = f) :
    (Scheme.Modules.pushforward g).obj (Line.Bundles.structureModule Y) ⟶
      (Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule X) :=
  structurePushforwardMorphism a g ≫ (Scheme.Modules.pushforwardCongr ha).hom.app (Line.Bundles.structureModule X)

theorem overMorphism_preimage_le (a : X ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S)
    (ha : a ≫ g = f) (U : S.Opens) : f ⁻¹ᵁ U ≤ a ⁻¹ᵁ (g ⁻¹ᵁ U) := by
  intro x hx
  change g (a x) ∈ U
  have h : g (a x) = f x := congrArg (fun k : X ⟶ S => k x) ha
  exact (congrArg (fun y : S => y ∈ U) h).mpr hx

theorem structurePushforwardOverMorphism_app (a : X ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S)
    (ha : a ≫ g = f) (U : S.Opens) (s : Γ(Y, g ⁻¹ᵁ U)) :
    (structurePushforwardOverMorphism a f g ha).app U s =
      a.appLE (g ⁻¹ᵁ U) (f ⁻¹ᵁ U) (overMorphism_preimage_le a f g ha U) s := by
  subst f
  change X.presheaf.map (𝟙 (.op (a ⁻¹ᵁ (g ⁻¹ᵁ U)))) (a.app (g ⁻¹ᵁ U) s) = _
  exact (ConcreteCategory.congr_hom (X.presheaf.map_id _) (a.app (g ⁻¹ᵁ U) s)).trans
    (ConcreteCategory.congr_hom a.app_eq_appLE s)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.PushforwardMorphism
