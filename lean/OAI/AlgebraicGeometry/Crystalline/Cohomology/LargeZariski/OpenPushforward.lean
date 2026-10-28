import OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.OpenInjectives
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.Topology.Sheaves.Functors

/-! # Open Pushforward -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.OpenPushforward.LargeZariskiOpenPushforward

noncomputable section

/-! # Actual open direct image preserves injective native-size module sheaves -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (R : Type (u + 1)) [CommRing R] {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.OpenInjectives.LargeZariskiOpenInjectives.Modules R

def functor : Sheaf (Opens.grothendieckTopology Y) V ⥤ Sheaf (Opens.grothendieckTopology X) V :=
  TopCat.Sheaf.pushforward V f.base

def adjunction : MixedCech.CechRestriction.MixedCechRestriction.sheafRestrictionFunctor R f ⊣ functor R f :=
  (f.opensFunctorAdjunction.op.whiskerLeft V).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) V)
    (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology Y) V)
    (Iso.refl _) (Iso.refl _)

instance preservesInjectives : (functor R f).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (adjunction R f)

def intersection (U : X.Opens) : Sheaf (Opens.grothendieckTopology X) V ⥤
    Sheaf (Opens.grothendieckTopology X) V :=
  MixedCech.CechRestriction.MixedCechRestriction.sheafRestrictionFunctor R U.ι ⋙ functor R U.ι

instance intersection_preservesInjectives (U : X.Opens) :
    (intersection R U).PreservesInjectiveObjects := by
  unfold intersection
  infer_instance

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.OpenPushforward.LargeZariskiOpenPushforward
