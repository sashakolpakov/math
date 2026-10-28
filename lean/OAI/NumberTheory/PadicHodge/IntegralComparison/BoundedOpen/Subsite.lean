import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.OpenCondition
import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SubsiteExtension

/-! # Subsite -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Subsite

noncomputable section

/-!
# IntegralComparison: exact restriction to original bounded crystalline objects over a geometric chart
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (g : X ⟶ Y) (n : ℕ)

def property : ObjectProperty (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n) :=
  fun U => Crystalline.OpenCondition.property g U.obj

theorem incoming {U V : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n}
    (α : U ⟶ V) (hV : property fY g n V) : property fY g n U :=
  Crystalline.OpenCondition.incoming g α.hom hV

abbrev Objects := (property (p := p) (J := J) (δ := δ) fY g n).FullSubcategory

abbrev inclusion : Objects (p := p) (J := J) (δ := δ) fY g n ⥤
    BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n :=
  (property fY g n).ι

def topology : GrothendieckTopology (Objects (p := p) (J := J) (δ := δ) fY g n) :=
  (inclusion fY g n).restrictedTopology (BoundedCrystalline.Site.topology fY n)

instance continuous : (inclusion (p := p) (J := J) (δ := δ) fY g n).IsContinuous
    (topology fY g n) (BoundedCrystalline.Site.topology fY n) :=
  Incoming.Subsite.continuous (property fY g n) (fun α => incoming fY g n α)
    (BoundedCrystalline.Site.topology fY n)

instance cocontinuous : (inclusion (p := p) (J := J) (δ := δ) fY g n).IsCocontinuous
    (topology fY g n) (BoundedCrystalline.Site.topology fY n) :=
  Incoming.Subsite.cocontinuous (property fY g n) (fun α => incoming fY g n α)
    (BoundedCrystalline.Site.topology fY n)

abbrev ModuleSheaf := Sheaf (topology (p := p) (J := J) (δ := δ) fY g n)
  (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))

abbrev restriction : BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fY n ⥤
    ModuleSheaf (p := p) (J := J) (δ := δ) fY g n :=
  (inclusion fY g n).sheafPushforwardContinuous (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))
    (topology fY g n) (BoundedCrystalline.Site.topology fY n)

instance restriction_additive : (restriction (p := p) (J := J) (δ := δ) fY g n).Additive where
  map_add := by intros; rfl

instance restriction_linear : (restriction (p := p) (J := J) (δ := δ) fY g n).Linear (Crystalline.ExactRestriction.Coeff (B := B)) where
  map_smul := by intros; rfl

instance restriction_leftAdjoint : (restriction (p := p) (J := J) (δ := δ) fY g n).IsLeftAdjoint :=
  ((inclusion fY g n).sheafAdjunctionCocontinuous (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))
    (topology fY g n) (BoundedCrystalline.Site.topology fY n)).isLeftAdjoint

instance restriction_preservesFiniteLimits :
    PreservesFiniteLimits (restriction (p := p) (J := J) (δ := δ) fY g n) := by infer_instance

instance restriction_preservesFiniteColimits :
    PreservesFiniteColimits (restriction (p := p) (J := J) (δ := δ) fY g n) := by infer_instance

abbrev extension : ModuleSheaf (p := p) (J := J) (δ := δ) fY g n ⥤
    BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fY n :=
  (inclusion fY g n).sheafPullback (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))
    (topology fY g n) (BoundedCrystalline.Site.topology fY n)

def adjunction : extension (p := p) (J := J) (δ := δ) fY g n ⊣ restriction fY g n :=
  (inclusion fY g n).sheafAdjunctionContinuous (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))
    (topology fY g n) (BoundedCrystalline.Site.topology fY n)

instance extension_preservesFiniteLimits :
    PreservesFiniteLimits (extension (p := p) (J := J) (δ := δ) fY g n) := by
  let P := property (p := p) (J := J) (δ := δ) fY g n
  let : P.ι.IsContinuous (P.ι.restrictedTopology (BoundedCrystalline.Site.topology fY n))
      (BoundedCrystalline.Site.topology fY n) :=
    Incoming.Subsite.continuous P (fun α => incoming fY g n α) (BoundedCrystalline.Site.topology fY n)
  exact Incoming.SubsiteExtension.sheafPullback_preservesFiniteLimits.{u + 1, u}
    P (fun α => incoming fY g n α) (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology fY n)

instance extension_leftAdjoint : (extension (p := p) (J := J) (δ := δ) fY g n).IsLeftAdjoint :=
  (adjunction fY g n).isLeftAdjoint

instance extension_preservesFiniteColimits :
    PreservesFiniteColimits (extension (p := p) (J := J) (δ := δ) fY g n) := by infer_instance

instance restriction_preservesInjectives :
    (restriction (p := p) (J := J) (δ := δ) fY g n).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (adjunction fY g n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Subsite
