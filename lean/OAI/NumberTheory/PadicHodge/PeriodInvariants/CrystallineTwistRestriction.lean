import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist
import OAI.NumberTheory.PadicHodge.PeriodInvariants.EquivalenceSites
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

/-! # Crystalline Twist Restriction -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistRestriction

noncomputable section

/-!
# Exact restriction along crystalline base twists

The equivalence on actual divided-power thickenings is continuous and
cocontinuous, since it preserves the generating coverings in both
directions. Its restriction on module sheaves is consequently exact.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} {f f' : X ⟶ Spec (CommRingCat.of B)}
variable (e : B ≃+* B) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
  (he' : DividedPowers.IsDPMorphism δ δ e.symm.toRingHom)
  (h : f' = f ≫ Spec.map (CommRingCat.ofHom e.toRingHom))

include he' in
theorem twist_continuous : (CrystallineBaseTwist.twist (p := p) e he h).IsContinuous IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology :=
  EquivalenceSites.continuous (CrystallineBaseTwist.twistEquivalence e he he' h) _ _
    (CrystallineBaseTwist.twist_preserves_coverings e he h)

include he' in
theorem twist_cocontinuous : (CrystallineBaseTwist.twist (p := p) e he h).IsCocontinuous IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology :=
  EquivalenceSites.cocontinuous (CrystallineBaseTwist.twistEquivalence e he he' h) _ _
    (CrystallineBaseTwist.twist_preserves_coverings e.symm he' (CrystallineBaseTwist.inverse_structure e h))

def restriction : IntegralComparison.Crystalline.ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f' ⥤
    IntegralComparison.Crystalline.ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f :=
  letI := twist_continuous (p := p) e he he' h
  (CrystallineBaseTwist.twist e he h).sheafPushforwardContinuous (ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)))
    IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology

instance restriction_additive : (restriction (p := p) e he he' h).Additive where
  map_add := by intros; rfl

instance restriction_linear : (restriction (p := p) e he he' h).Linear (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) where
  map_smul := by intros; rfl

instance restriction_rightAdjoint : (restriction (p := p) e he he' h).IsRightAdjoint := by
  let := twist_continuous (p := p) e he he' h
  dsimp only [restriction]
  infer_instance

instance restriction_leftAdjoint : (restriction (p := p) e he he' h).IsLeftAdjoint := by
  let := twist_continuous (p := p) e he he' h
  let := twist_cocontinuous (p := p) e he he' h
  exact ((CrystallineBaseTwist.twist e he h).sheafAdjunctionCocontinuous (ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)))
    IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology).isLeftAdjoint

instance restriction_preservesFiniteLimits :
    PreservesFiniteLimits (restriction (p := p) e he he' h) := by infer_instance

instance restriction_preservesFiniteColimits :
    PreservesFiniteColimits (restriction (p := p) e he he' h) := by infer_instance

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistRestriction
