import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Subsite
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SheafInjectives

/-! # Sheaf Injectives -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SheafInjectives

noncomputable section

/-!
# IntegralComparison: injective resolutions on bounded crystalline sites and geometric subsites
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

private lemma moduleSheavesGrothendieck (C : Type (u + 1)) [Category.{u} C]
    (T : GrothendieckTopology C) (R : Type (u + 1)) [Ring R] :
    IsGrothendieckAbelian.{u + 1} (Sheaf T (ModuleCat.{u + 1} R)) := by
  let : SmallCategory (SmallModel.{u + 1} C) := smallCategorySmallModel.{u + 1, u, u + 1} C
  let e := equivSmallModel.{u + 1} C
  let K := e.inverse.inducedTopology T
  have : HasSheafify K (ModuleCat.{u + 1} R) :=
    HasSheafify.mk' K (ModuleCat.{u + 1} R)
      (plusPlusAdjunction.{u + 1, u + 1, u + 2, u + 1, u + 1, u + 1}
        K (ModuleCat.{u + 1} R))
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1, u + 1, u, u + 2, u + 1}
    T (ModuleCat.{u + 1} R)

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (g : X ⟶ Y) (n : ℕ)

instance boundedGrothendieck : IsGrothendieckAbelian.{u + 1}
    (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fY n) :=
  moduleSheavesGrothendieck (BoundedCrystalline.Site.Objects fY n)
    (BoundedCrystalline.Site.topology fY n) (Crystalline.ExactRestriction.Coeff (B := B))

instance openGrothendieck : IsGrothendieckAbelian.{u + 1}
    (BoundedOpen.Subsite.ModuleSheaf (p := p) (J := J) (δ := δ) fY g n) :=
  moduleSheavesGrothendieck (BoundedOpen.Subsite.Objects fY g n)
    (BoundedOpen.Subsite.topology fY g n) (Crystalline.ExactRestriction.Coeff (B := B))

instance boundedEnoughInjectives : EnoughInjectives
    (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fY n) := by
  infer_instance

instance openEnoughInjectives : EnoughInjectives
    (BoundedOpen.Subsite.ModuleSheaf (p := p) (J := J) (δ := δ) fY g n) := by
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SheafInjectives
