import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

/-! # Ambient Faithful -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.AmbientFaithful.CrystallineAmbientFaithful

noncomputable section

/-! Maps of original crystalline objects are determined by their actual
ambient scheme maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}

theorem ringHom_injective {A R : Type u} [CommRing A] [CommRing R] {φ ψ : A →+* R}
    (h : Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom ψ)) : φ = ψ :=
  congrArg CommRingCat.Hom.hom (Quiver.Hom.op_inj (Scheme.Spec.map_injective h))

theorem hom_ext {U V : IntegralComparison.BigCrystallineSite.Object p B J δ f} {α β : U ⟶ V}
    (h : IntegralComparison.BigCrystallineSite.Object.ambient.map α = IntegralComparison.BigCrystallineSite.Object.ambient.map β) : α = β := by
  have hr : CommRingCat.ofHom α.ringMap.toRingHom = CommRingCat.ofHom β.ringMap.toRingHom :=
    Quiver.Hom.op_inj (Scheme.Spec.map_injective h)
  apply IntegralComparison.BigCrystallineSite.Object.Hom.ext
  ext x
  exact ConcreteCategory.congr_hom hr x

instance faithful : (IntegralComparison.BigCrystallineSite.Object.ambient (p := p) (B := B) (J := J) (δ := δ) (f := f)).Faithful where
  map_injective := hom_ext

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.AmbientFaithful.CrystallineAmbientFaithful
