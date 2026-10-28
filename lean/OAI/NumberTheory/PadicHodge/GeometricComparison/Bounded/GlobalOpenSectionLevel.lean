import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.GlobalSectionRestriction
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.OpenSectionLevel
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.PresheafSectionRestriction

/-! # Global Open Section Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.GlobalOpenSectionLevel.BoundedGlobalOpenSectionLevel

noncomputable section

/-! Restricting actual global sections to an open commutes with
restriction between bounded crystalline levels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of B)) (n m : ℕ) (hnm : n ≤ m)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p) (J := J) (δ := δ) f n m hnm

theorem natural : GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation (p := p) (J := J) (δ := δ) f m ≫
    OpenSectionLevel.BoundedOpenSectionLevel.transformation f n m hnm =
      Functor.whiskerRight (IntegralComparison.Sheaf.PresheafSectionRestriction.map G R (IntegralComparison.BoundedCrystalline.Site.topology f n) (IntegralComparison.BoundedCrystalline.Site.topology f m))
        (Functor.const Y.Opensᵒᵖ) ≫
          Functor.whiskerLeft T (GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation f n) := by
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.GlobalOpenSectionLevel.BoundedGlobalOpenSectionLevel
