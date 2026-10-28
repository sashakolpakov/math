import OAI.NumberTheory.PadicHodge.GeometricComparison.BaseGenerated
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.AmbientFaithful

/-! # Open Factor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.OpenFactor.CrystallineOpenFactor

noncomputable section

/-! Ambient open factorization into a base-generated frame lifts to an
actual factorization in the original crystalline category. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
  {U V T : IntegralComparison.BigCrystallineSite.Object p B J δ f} (α : U ⟶ V) (β : T ⟶ V)
  [IsOpenImmersion (IntegralComparison.BigCrystallineSite.Object.ambient.map α)]
  (hgen : U.ideal = J.map U.base)
  (hrange : Set.range (IntegralComparison.BigCrystallineSite.Object.ambient.map β) ⊆ Set.range (IntegralComparison.BigCrystallineSite.Object.ambient.map α))

def schemeLift : IntegralComparison.BigCrystallineSite.Object.ambient.obj T ⟶ IntegralComparison.BigCrystallineSite.Object.ambient.obj U :=
  IsOpenImmersion.lift (IntegralComparison.BigCrystallineSite.Object.ambient.map α) (IntegralComparison.BigCrystallineSite.Object.ambient.map β) hrange

def ringLift : U.ring →+* T.ring :=
  (Scheme.Spec.preimage (X := op T.ring) (Y := op U.ring) (schemeLift α β hrange)).unop.hom

theorem spec_ringLift : Spec.map (CommRingCat.ofHom (ringLift α β hrange)) = schemeLift α β hrange :=
  Scheme.Spec.map_preimage (X := op T.ring) (Y := op U.ring) (schemeLift α β hrange)

theorem ringLift_comp : (ringLift α β hrange).comp α.ringMap.toRingHom = β.ringMap.toRingHom := by
  apply AmbientFaithful.CrystallineAmbientFaithful.ringHom_injective
  rw [CommRingCat.ofHom_comp, Spec.map_comp, spec_ringLift]
  exact IsOpenImmersion.lift_fac (IntegralComparison.BigCrystallineSite.Object.ambient.map α) (IntegralComparison.BigCrystallineSite.Object.ambient.map β) hrange

def lift : T ⟶ U := BaseGenerated.BaseGeneratedFrameLift.lift α β hgen (ringLift α β hrange)
  (ringLift_comp α β hrange)

theorem lift_comp : CrystallineOpenFactor.lift α β hgen hrange ≫ α = β :=
  BaseGenerated.BaseGeneratedFrameLift.lift_comp α β hgen (ringLift α β hrange) (ringLift_comp α β hrange)

theorem unique (γ : T ⟶ U) (hγ : γ ≫ α = β) : γ = CrystallineOpenFactor.lift α β hgen hrange := by
  apply AmbientFaithful.CrystallineAmbientFaithful.hom_ext
  apply (cancel_mono (IntegralComparison.BigCrystallineSite.Object.ambient.map α)).mp
  rw [← IntegralComparison.BigCrystallineSite.Object.ambient.map_comp, ← IntegralComparison.BigCrystallineSite.Object.ambient.map_comp, hγ, lift_comp]

include hgen hrange in
theorem exists_factor : ∃ γ : T ⟶ U, γ ≫ α = β :=
  ⟨CrystallineOpenFactor.lift α β hgen hrange, lift_comp α β hgen hrange⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.OpenFactor.CrystallineOpenFactor
