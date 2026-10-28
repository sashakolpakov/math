import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.AmbientFaithful
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

/-! # Ambient Mono -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.AmbientMono.BoundedAmbientMono

noncomputable section

/-! An open ambient map is a monomorphism in the actual bounded crystalline category. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {n : ℕ}
  {U V : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n} (α : U ⟶ V)

theorem mono (h : IsOpenImmersion (IntegralComparison.BigCrystallineSite.Object.ambient.map α.hom)) : Mono α := by
  let := h
  have hm : Mono α.hom := IntegralComparison.BigCrystallineSite.Object.ambient.mono_of_mono_map inferInstance
  exact (IntegralComparison.BoundedCrystalline.Site.inclusion f n).mono_of_mono_map hm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.AmbientMono.BoundedAmbientMono
