import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.PushforwardFunctor

/-! # Pushforward Base Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.PushforwardBaseComposition

noncomputable section

/-! Pullback of functions on pushed-forward structure sheaves commutes with further direct image. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem structurePushforwardOverMorphism_congr {X Y S : Scheme.{u}}
    (a a' : X ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S)
    (ha : a ≫ g = f) (ha' : a' ≫ g = f) (h : a = a') :
    PushforwardMorphism.structurePushforwardOverMorphism a f g ha =
      PushforwardMorphism.structurePushforwardOverMorphism a' f g ha' := by
  subst a'
  rfl

theorem structurePushforwardOverMorphism_pushforward_comp {X Y S T : Scheme.{u}}
    (a : X ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (q : S ⟶ T) (ha : a ≫ g = f) :
    (Scheme.Modules.pushforward q).map (PushforwardMorphism.structurePushforwardOverMorphism a f g ha) ≫
        (Scheme.Modules.pushforwardComp f q).hom.app (Line.Bundles.structureModule X) =
      (Scheme.Modules.pushforwardComp g q).hom.app (Line.Bundles.structureModule Y) ≫
        PushforwardMorphism.structurePushforwardOverMorphism a (f ≫ q) (g ≫ q)
          ((Category.assoc a g q).symm.trans (congrArg (fun z => z ≫ q) ha)) := by
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.PushforwardBaseComposition
