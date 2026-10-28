import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SubsiteExtension

/-! # Extension -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Extension

noncomputable section

/-!
# IntegralComparison: exact bounded-level extension and preservation of injectives
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n : ℕ)

abbrev extension : Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n ⥤
    Crystalline.ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f :=
  (Site.inclusion f n).sheafPullback (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) (Site.topology f n) BigCrystallineSite.Object.topology

def adjunction : extension (p := p) (J := J) (δ := δ) f n ⊣ Site.restriction f n :=
  (Site.inclusion f n).sheafAdjunctionContinuous (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))
    (Site.topology f n) BigCrystallineSite.Object.topology

instance extension_preservesFiniteLimits :
    PreservesFiniteLimits (extension (p := p) (J := J) (δ := δ) f n) := by
  let P : ObjectProperty (BigCrystallineSite.Object p B J δ f) := Site.property f n
  have : P.ι.IsContinuous (P.ι.restrictedTopology BigCrystallineSite.Object.topology) BigCrystallineSite.Object.topology :=
    Incoming.Subsite.continuous P (fun α => Site.property_of_hom f n α) BigCrystallineSite.Object.topology
  exact Incoming.SubsiteExtension.sheafPullback_preservesFiniteLimits.{u + 1, u}
    P (fun α => Site.property_of_hom f n α) (Crystalline.ExactRestriction.Coeff (B := B)) BigCrystallineSite.Object.topology

instance extension_leftAdjoint : (extension (p := p) (J := J) (δ := δ) f n).IsLeftAdjoint :=
  (adjunction f n).isLeftAdjoint

instance extension_preservesFiniteColimits :
    PreservesFiniteColimits (extension (p := p) (J := J) (δ := δ) f n) := by infer_instance

instance restriction_preservesInjectives :
    (Site.restriction (p := p) (J := J) (δ := δ) f n).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (adjunction f n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Extension
