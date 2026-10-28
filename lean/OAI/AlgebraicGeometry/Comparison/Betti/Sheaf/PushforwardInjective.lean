import OAI.AlgebraicGeometry.SheafCohomology.Cech.TopCatRestrict
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Pushforward Injective -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.PushforwardInjective.Cech

noncomputable section

/-! The actual direct-image functor on abelian sheaves preserves injectives. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

instance additiveSheafPullback_preservesFiniteLimits :
    PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) := by
  exact Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat
    (Opens.map f) AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

instance additiveSheafPushforward_preservesInjectiveObjects :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.PushforwardInjective.Cech
