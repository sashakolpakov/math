import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheafFunctor
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Pushforward Pullback Refinement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PushforwardPullbackRefinement

noncomputable section

/-! Refining a scheme over a fixed target gives an actual map from a direct image to the direct image of the pulled-back module. Its values are the pullback adjunction unit. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

def pushforwardPullbackRefinementMap (M : Y.Modules) :
    (Scheme.Modules.pushforward g).obj M ⟶
      (Scheme.Modules.pushforward (f ≫ g)).obj ((Scheme.Modules.pullback f).obj M) :=
  (Scheme.Modules.pushforward g).map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
    (Scheme.Modules.pushforwardComp f g).hom.app ((Scheme.Modules.pullback f).obj M)

theorem pushforwardPullbackRefinementMap_apply (M : Y.Modules) (U : Z.Opens)
    (m : Γ(M, g ⁻¹ᵁ U)) :
    (pushforwardPullbackRefinementMap f g M).app U m =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app (g ⁻¹ᵁ U) m := rfl

theorem pushforwardPullbackRefinementMap_naturality {M N : Y.Modules} (a : M ⟶ N) :
    (Scheme.Modules.pushforward g).map a ≫ pushforwardPullbackRefinementMap f g N =
      pushforwardPullbackRefinementMap f g M ≫
        (Scheme.Modules.pushforward (f ≫ g)).map ((Scheme.Modules.pullback f).map a) := by
  have hu : a ≫ (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
        (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map a) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality a
  dsimp only [pushforwardPullbackRefinementMap]
  rw [← Category.assoc, ← Functor.map_comp, hu, Functor.map_comp, Category.assoc]
  exact congrArg
    (fun k => (Scheme.Modules.pushforward g).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫ k)
    ((Scheme.Modules.pushforwardComp f g).hom.naturality ((Scheme.Modules.pullback f).map a))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PushforwardPullbackRefinement
