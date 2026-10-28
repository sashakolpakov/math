import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives
import Mathlib.Topology.Sheaves.Functors

/-! # Abelian Sheaf Pullback -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction

noncomputable section

/-! Exact inverse image and preservation of injectives by direct image for abelian sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

abbrev abelianSheafPullback : AbelianSheafInjectives.Construction.AbelianSheaves Y ⥤ AbelianSheafInjectives.Construction.AbelianSheaves X :=
  (Opens.map f).sheafPullback AddCommGrpCat (_root_.Opens.grothendieckTopology Y)
    (_root_.Opens.grothendieckTopology X)

abbrev abelianSheafPushforward : AbelianSheafInjectives.Construction.AbelianSheaves X ⥤ AbelianSheafInjectives.Construction.AbelianSheaves Y :=
  (Opens.map f).sheafPushforwardContinuous AddCommGrpCat (_root_.Opens.grothendieckTopology Y)
    (_root_.Opens.grothendieckTopology X)

def abelianSheafPullbackAdjunction : abelianSheafPullback f ⊣ abelianSheafPushforward f :=
  (Opens.map f).sheafAdjunctionContinuous _ _ _

attribute [local instance] reflectsLimits_of_reflectsIsomorphisms in
instance abelianSheafPullback_preservesFiniteLimits : PreservesFiniteLimits (abelianSheafPullback f) := by
  apply Functor.sheafPullbackConstruction.preservesFiniteLimits

instance abelianSheafPullback_isLeftAdjoint : (abelianSheafPullback f).IsLeftAdjoint :=
  (abelianSheafPullbackAdjunction f).isLeftAdjoint

instance abelianSheafPushforward_isRightAdjoint : (abelianSheafPushforward f).IsRightAdjoint :=
  (abelianSheafPullbackAdjunction f).isRightAdjoint

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts in
instance abelianSheafPullback_additive : (abelianSheafPullback f).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

theorem abelianSheafPullback_shortExact (S : ShortComplex (AbelianSheafInjectives.Construction.AbelianSheaves Y)) (hS : S.ShortExact) :
    (S.map (abelianSheafPullback f)).ShortExact := hS.map_of_exact _

theorem injective_abelianSheafPushforward (I : AbelianSheafInjectives.Construction.AbelianSheaves X) [Injective I] :
    Injective ((abelianSheafPushforward f).obj I) :=
  Injective.injective_of_adjoint (abelianSheafPullbackAdjunction f) I

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction
