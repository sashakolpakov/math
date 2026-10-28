import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SeparatedProductLift
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SliceStructure
import OAI.NumberTheory.PadicHodge.IntegralComparison.SliceExactExtension
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Slice Image -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SliceImage

noncomputable section

/-!
# IntegralComparison: actual direct image from a crystalline slice

The proved products over a separated scheme give the right adjoint to
the crystalline slice-forgetful functor. The resulting direct image on
the original module sheaves is right adjoint to exact slice restriction
and preserves injectives.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f]

instance bigBinaryProducts : HasBinaryProducts (BigCrystallineSite.Object p B J δ f) := by
  have (U V : BigCrystallineSite.Object p B J δ f) : HasBinaryProduct U V :=
    HasLimit.mk ⟨SeparatedProductLift.fan f U V (Fact.out : p.Prime).pos,
      SeparatedProductLift.isProduct f U V (Fact.out : p.Prime).pos⟩
  exact hasBinaryProducts_of_hasLimit_pair _

variable (U : BigCrystallineSite.Object p B J δ f)

abbrev SliceSheaf := Sheaf (BigCrystallineSite.Object.topology.over U) (ModuleCat.{u + 1} (ExactRestriction.Coeff (B := B)))

abbrev restriction : ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f ⥤ SliceSheaf f U :=
  BigCrystallineSite.Object.topology.overPullback (ModuleCat.{u + 1} (ExactRestriction.Coeff (B := B))) U

abbrev directImage : SliceSheaf f U ⥤ ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f :=
  (Over.star U).sheafPushforwardContinuous (ModuleCat.{u + 1} (ExactRestriction.Coeff (B := B)))
    BigCrystallineSite.Object.topology (BigCrystallineSite.Object.topology.over U)

def adjunction : restriction f U ⊣ directImage f U :=
  (Over.forgetAdjStar U).sheafPushforwardContinuous (E := ModuleCat.{u + 1} (ExactRestriction.Coeff (B := B)))
    (BigCrystallineSite.Object.topology.over U) BigCrystallineSite.Object.topology

instance restriction_leftAdjoint : (restriction f U).IsLeftAdjoint :=
  ((Over.forget U).sheafAdjunctionCocontinuous (ModuleCat.{u + 1} (ExactRestriction.Coeff (B := B)))
    (BigCrystallineSite.Object.topology.over U) BigCrystallineSite.Object.topology).isLeftAdjoint

instance restriction_rightAdjoint : (restriction f U).IsRightAdjoint :=
  ((Over.forget U).sheafAdjunctionContinuous (ModuleCat.{u + 1} (ExactRestriction.Coeff (B := B)))
    (BigCrystallineSite.Object.topology.over U) BigCrystallineSite.Object.topology).isRightAdjoint

instance restriction_preservesFiniteLimits : PreservesFiniteLimits (restriction f U) := by infer_instance

instance restriction_preservesFiniteColimits : PreservesFiniteColimits (restriction f U) := by infer_instance

instance restriction_additive : (restriction f U).Additive where
  map_add := by intros; rfl

instance restriction_preservesInjectives : (restriction f U).PreservesInjectiveObjects :=
  SliceExactExtension.restriction_preservesInjectives.{u + 1, u}
    (ExactRestriction.Coeff (B := B)) U BigCrystallineSite.Object.topology

instance directImage_rightAdjoint : (directImage f U).IsRightAdjoint := (adjunction f U).isRightAdjoint

instance directImage_additive : (directImage f U).Additive where
  map_add := by intros; rfl

instance directImage_preservesFiniteLimits : PreservesFiniteLimits (directImage f U) := by infer_instance

instance directImage_preservesInjectives : (directImage f U).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (adjunction f U)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SliceImage
