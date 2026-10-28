import OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.PrincipalPullback

/-! # Cartesian Maps -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CartesianMaps

noncomputable section

/-!
# IntegralComparison: cartesian crystalline morphisms under composition and localization
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalizationMaps

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
variable {U V W : BigCrystallineSite.Object p B J δ f}

lemma cartesian_comp (α : U ⟶ V) (β : V ⟶ W) (hα : BigCrystallineSite.Object.Cartesian α)
    (hβ : BigCrystallineSite.Object.Cartesian β) : BigCrystallineSite.Object.Cartesian (α ≫ β) := by
  unfold BigCrystallineSite.Object.Cartesian at hα hβ ⊢
  rw [BigCrystallineSite.Object.closed.map_comp, BigCrystallineSite.Object.ambient.map_comp]
  exact hα.paste_horiz hβ

lemma cartesian_of_comp (α : U ⟶ V) (β : V ⟶ W) (h : BigCrystallineSite.Object.Cartesian (α ≫ β))
    (hβ : BigCrystallineSite.Object.Cartesian β) : BigCrystallineSite.Object.Cartesian α := by
  unfold BigCrystallineSite.Object.Cartesian at h hβ ⊢
  rw [BigCrystallineSite.Object.closed.map_comp, BigCrystallineSite.Object.ambient.map_comp] at h
  exact h.of_right (BigCrystallineSite.Object.closedImmersion.naturality α) hβ

lemma localizedHom_cartesian (α : U ⟶ V) (hα : BigCrystallineSite.Object.Cartesian α) (r : V.ring) :
    BigCrystallineSite.Object.Cartesian (LocalizationMaps.localizedHom α r) := by
  have h := cartesian_comp (Localization.hom U (α.ringMap r)) α (Localization.hom_cartesian _ _) hα
  rw [← LocalizationMaps.localizedHom_square] at h
  exact cartesian_of_comp (LocalizationMaps.localizedHom α r) (Localization.hom V r) h (Localization.hom_cartesian _ _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CartesianMaps
