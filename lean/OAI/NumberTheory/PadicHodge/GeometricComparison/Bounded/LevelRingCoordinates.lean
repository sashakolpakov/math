import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps

/-! # Level Ring Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LevelRingCoordinates.BoundedLevelRingCoordinates

noncomputable section

/-! Bounded-level inclusions retain the original unapplied ring homomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n m : ℕ) (hnm : n ≤ m)
  {F F' : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n} (a : F ⟶ F')

theorem ringHom :
    ((IntegralComparison.BoundedCrystalline.LevelMaps.inclusion f n m hnm).map a).hom.ringMap.toRingHom =
      a.hom.ringMap.toRingHom := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LevelRingCoordinates.BoundedLevelRingCoordinates
