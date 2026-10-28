import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.SheafLocalExactness
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Pushforward Injective -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Module.PushforwardInjective.ModulePushforwardInjective

noncomputable section

/-! Direct image of module sheaves preserves injectives through the exact inverse-image adjunction. -/

open _root_.CategoryTheory Limits _root_.TopologicalSpace

universe u

variable (R : Type u) [CommRing R] {X Y : TopCat.{u}} (f : X ⟶ Y)

instance pullback_preservesFiniteLimits :
    PreservesFiniteLimits (TopCat.Sheaf.pullback (ModuleCat.{u} R) f) :=
  Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat
    (Opens.map f) (ModuleCat.{u} R)
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

instance pushforward_preservesInjectiveObjects :
    (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) f)

instance pushforward_additive : (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f).Additive where
  map_add := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Module.PushforwardInjective.ModulePushforwardInjective
