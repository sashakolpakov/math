import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.TwistSheafIdentity
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.TwistEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SheafInjectives

/-! # Twist Cohomology Identity -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.TwistCohomologyIdentity.CrystallineTwistIdentity

noncomputable section

/-! The actual identity base twist induces the identity on crystalline cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))
  (he : DividedPowers.IsDPMorphism δ δ (RingEquiv.refl B).toRingHom)

theorem cohomologyMap_refl (n : ℕ) (x : IntegralComparison.BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n) :
    PeriodInvariants.CrystallineTwistCohomology.cohomologyMap (RingEquiv.refl B) he he (TwistIdentity.CrystallineTwistIdentity.identity_over f) n x = x := by
  let F := PeriodInvariants.CrystallineTwistCohomology.twistedRestriction (p := p)
    (RingEquiv.refl B) he he (TwistIdentity.CrystallineTwistIdentity.identity_over f)
  let : F.Additive := PeriodInvariants.CrystallineTwistCohomology.twistedRestriction_additive _ _ _ _
  let : PreservesFiniteLimits F := PeriodInvariants.CrystallineTwistCohomology.twistedRestriction_preservesFiniteLimits _ _ _ _
  let : PreservesFiniteColimits F := PeriodInvariants.CrystallineTwistCohomology.twistedRestriction_preservesFiniteColimits _ _ _ _
  let s := PeriodInvariants.CrystallineTwistCohomology.constantTransport (p := p)
    (RingEquiv.refl B) he he (TwistIdentity.CrystallineTwistIdentity.identity_over f)
  let t := PeriodInvariants.CrystallineTwistCohomology.structureTransport (p := p)
    (RingEquiv.refl B) he he (TwistIdentity.CrystallineTwistIdentity.identity_over f)
  have h₁ := TwistEvaluation.CrystallineTwistIdentity.cohomologyMap_apply (RingEquiv.refl B) he he (TwistIdentity.CrystallineTwistIdentity.identity_over f) n x
  have hF : F = 𝟭 _ := TwistIdentity.CrystallineTwistIdentity.twistedRestriction_refl f he
  have h₂ := TwistEvaluation.CrystallineTwistIdentity.ext_functor_eq_id (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) F hF s t
    (TwistSheafIdentity.CrystallineTwistIdentity.constantTransport_refl f he) (TwistSheafIdentity.CrystallineTwistIdentity.structureTransport_refl f he) x
  exact h₁.trans h₂

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.TwistCohomologyIdentity.CrystallineTwistIdentity
