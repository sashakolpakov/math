import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

/-! # Ambient Formula -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.AmbientFormula.CrystallineAmbientFormula

noncomputable section

/-! The original ambient functor acts by the actual underlying divided-power ring map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {n : ℕ}

theorem map {U V : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n} (α : U ⟶ V) :
    IntegralComparison.BigCrystallineSite.Object.ambient.map α.hom = Spec.map (CommRingCat.ofHom α.hom.ringMap.toRingHom) := rfl

theorem openImmersion {U V : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n} (α : U ⟶ V)
    (h : IsOpenImmersion (Spec.map (CommRingCat.ofHom α.hom.ringMap.toRingHom))) :
    IsOpenImmersion (IntegralComparison.BigCrystallineSite.Object.ambient.map α.hom) := by
  rw [CrystallineAmbientFormula.map]
  exact h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.AmbientFormula.CrystallineAmbientFormula
