import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.TwistIdentity
import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafCoefficientId

/-! # Twist Sheaf Identity -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.TwistSheafIdentity.CrystallineTwistIdentity

noncomputable section

/-! Identity normalization of the actual structure and constant sheaves in crystalline base twist. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))
  (he : DividedPowers.IsDPMorphism δ δ (RingEquiv.refl B).toRingHom)

theorem presheafTransport_refl :
    PeriodInvariants.CrystallineTwistCohomology.presheafTransport (p := p) (RingEquiv.refl B) he (TwistIdentity.CrystallineTwistIdentity.identity_over f) =
      Iso.refl (IntegralComparison.BigCrystallineCohomology.largePresheaf f) := by
  apply Iso.ext
  ext U x
  rfl

theorem structureTransport_refl :
    PeriodInvariants.CrystallineTwistCohomology.structureTransport (p := p) (RingEquiv.refl B) he he (TwistIdentity.CrystallineTwistIdentity.identity_over f) =
      Iso.refl (IntegralComparison.BigCrystallineCohomology.structureSheaf f) := by
  let T := IntegralComparison.BigCrystallineSite.Object.topology (p := p) (J := J) (δ := δ) (f := f)
  let A := ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B))
  let P := IntegralComparison.BigCrystallineCohomology.largePresheaf (p := p) (J := J) (δ := δ) f
  change (𝟭 (IntegralComparison.Crystalline.ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f)).mapIso
      (PeriodInvariants.SheafificationCoherence.transport T T (𝟭 _) P) ≪≫
        ((sheafComposeNatIso T (𝟭 A) (sheafificationAdjunction T A)
          (sheafificationAdjunction T A)).app P).symm ≪≫
            (presheafToSheaf T A).mapIso
              (PeriodInvariants.CrystallineTwistCohomology.presheafTransport (p := p) (RingEquiv.refl B)
                he (TwistIdentity.CrystallineTwistIdentity.identity_over f)) = _
  erw [presheafTransport_refl, PeriodInvariants.SheafificationCoherence.transport_id,
    SheafCoefficientId.SheafCoefficientIdentity.sheafComposeNatIso_id, Functor.mapIso_refl, Functor.mapIso_refl]
  rfl

theorem constantTransport_refl :
    PeriodInvariants.CrystallineTwistCohomology.constantTransport (p := p) (RingEquiv.refl B) he he (TwistIdentity.CrystallineTwistIdentity.identity_over f) =
      Iso.refl (IntegralComparison.BigCrystallineCohomology.constantUnit f) := by
  let T := IntegralComparison.BigCrystallineSite.Object.topology (p := p) (J := J) (δ := δ) (f := f)
  let A := ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B))
  let m := ModuleCat.of (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B))
  change (𝟭 (IntegralComparison.Crystalline.ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f)).mapIso
      (PeriodInvariants.SheafificationCoherence.transport T T (𝟭 _) ((Functor.const _).obj m)) ≪≫
        (constantCommuteCompose T (𝟭 A)).app m ≪≫
          (constantSheaf T A).mapIso (Iso.refl m) = _
  erw [PeriodInvariants.SheafificationCoherence.transport_id, SheafCoefficientId.SheafCoefficientIdentity.constantCommuteCompose_id,
    Functor.mapIso_refl, Functor.mapIso_refl]
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.TwistSheafIdentity.CrystallineTwistIdentity
