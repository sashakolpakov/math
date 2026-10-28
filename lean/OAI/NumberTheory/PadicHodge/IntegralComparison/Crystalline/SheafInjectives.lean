import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Map

/-! # Sheaf Injectives -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SheafInjectives

noncomputable section

/-!
# IntegralComparison: enough injectives in the original crystalline module-sheaf categories

The sites are essentially small at the object universe. The categories
of module sheaves are Grothendieck abelian categories at that universe,
so the existing general construction supplies injective resolutions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction (Coeff ModuleSheaf)
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Map.Comparison (SmallModuleSheaf)

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

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

instance bigGrothendieck : IsGrothendieckAbelian.{u + 1} (ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f) :=
  moduleSheavesGrothendieck (BigCrystallineSite.Object p B J δ f) BigCrystallineSite.Object.topology (ExactRestriction.Coeff (B := B))

instance smallGrothendieck : IsGrothendieckAbelian.{u + 1} (Map.Comparison.SmallModuleSheaf (p := p) (J := J) (δ := δ) f) :=
  moduleSheavesGrothendieck (Site.AffineThickening p B J δ f) Site.AffineThickening.topology (ExactRestriction.Coeff (B := B))

instance bigEnoughInjectives : EnoughInjectives (ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f) := by infer_instance

instance smallEnoughInjectives : EnoughInjectives (Map.Comparison.SmallModuleSheaf (p := p) (J := J) (δ := δ) f) := by infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SheafInjectives
