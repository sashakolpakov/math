import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Products
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.SliceSheaves

/-! # Slice Image -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SliceImage

noncomputable section

/-!
# IntegralComparison: actual slice direct image inside each bounded crystalline level
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  (U : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

abbrev restriction : BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n ⥤
    BoundedCrystalline.SliceSheaves.SliceSheaf f n U :=
  (BoundedCrystalline.Site.topology f n).overPullback (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) U

abbrev directImage : BoundedCrystalline.SliceSheaves.SliceSheaf f n U ⥤
    BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n :=
  (Over.star U).sheafPushforwardContinuous (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))
    (BoundedCrystalline.Site.topology f n) ((BoundedCrystalline.Site.topology f n).over U)

def adjunction : restriction f n U ⊣ directImage f n U :=
  (Over.forgetAdjStar U).sheafPushforwardContinuous (E := ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))
    ((BoundedCrystalline.Site.topology f n).over U) (BoundedCrystalline.Site.topology f n)

instance restriction_leftAdjoint : (restriction f n U).IsLeftAdjoint :=
  ((Over.forget U).sheafAdjunctionCocontinuous (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))
    ((BoundedCrystalline.Site.topology f n).over U) (BoundedCrystalline.Site.topology f n)).isLeftAdjoint

instance restriction_preservesFiniteLimits : PreservesFiniteLimits (restriction f n U) := by infer_instance
instance restriction_preservesFiniteColimits : PreservesFiniteColimits (restriction f n U) := by infer_instance

instance restriction_additive : (restriction f n U).Additive where
  map_add := by intros; rfl

instance restriction_preservesInjectives : (restriction f n U).PreservesInjectiveObjects :=
  SliceExactExtension.restriction_preservesInjectives.{u + 1, u}
    (Crystalline.ExactRestriction.Coeff (B := B)) U (BoundedCrystalline.Site.topology f n)

instance directImage_rightAdjoint : (directImage f n U).IsRightAdjoint := (adjunction f n U).isRightAdjoint
instance directImage_preservesFiniteLimits : PreservesFiniteLimits (directImage f n U) := by infer_instance

instance directImage_additive : (directImage f n U).Additive where
  map_add := by intros; rfl

instance directImage_preservesInjectives : (directImage f n U).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (adjunction f n U)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SliceImage
