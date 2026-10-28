import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology

/-! # Twist Identity -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.TwistIdentity.CrystallineTwistIdentity

noncomputable section

/-! The actual crystalline base-twist site is unchanged for the identity coefficient automorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

theorem identity_over : f = f ≫ Spec.map (CommRingCat.ofHom (RingEquiv.refl B).toRingHom) := by
  change f = f ≫ Spec.map (𝟙 (CommRingCat.of B))
  rw [Spec.map_id, Category.comp_id]

theorem twist_refl (he : DividedPowers.IsDPMorphism δ δ (RingEquiv.refl B).toRingHom) :
    PeriodInvariants.CrystallineBaseTwist.twist (p := p) (RingEquiv.refl B) he (identity_over f) =
      𝟭 (IntegralComparison.BigCrystallineSite.Object p B J δ f) := rfl

theorem coefficientEquiv_refl :
    PeriodInvariants.CrystallineTwistCohomology.coefficientEquiv (RingEquiv.refl B) = RingEquiv.refl _ := by
  ext x
  rfl

theorem restriction_refl
    (he : DividedPowers.IsDPMorphism δ δ (RingEquiv.refl B).toRingHom) :
    PeriodInvariants.CrystallineTwistRestriction.restriction (p := p) (RingEquiv.refl B) he he (identity_over f) =
      𝟭 (IntegralComparison.Crystalline.ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f) := rfl

theorem twistedRestriction_refl
    (he : DividedPowers.IsDPMorphism δ δ (RingEquiv.refl B).toRingHom) :
    PeriodInvariants.CrystallineTwistCohomology.twistedRestriction (p := p) (RingEquiv.refl B) he he (identity_over f) =
      𝟭 (IntegralComparison.Crystalline.ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f) := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.TwistIdentity.CrystallineTwistIdentity
