import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Cocontinuous

/-! # Exact Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

noncomputable section

/-!
# IntegralComparison: exact restriction on big crystalline module sheaves

The proved continuity and cocontinuity give both adjoints to restriction.
Consequently restriction preserves finite limits and colimits and induces
linear maps on actual Ext groups of crystalline sheaves.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
variable {fY : Y ⟶ Spec (CommRingCat.of B)}

abbrev Coeff := ULift.{u + 1} B

abbrev ModuleSheaf (f : X ⟶ Spec (CommRingCat.of B)) :=
  Sheaf (BigCrystallineSite.Object.topology (p := p) (J := J) (δ := δ) (f := f)) (ModuleCat.{u + 1} (Coeff (B := B)))

instance hasExt : HasExt.{u + 2} (ModuleSheaf (p := p) (J := J) (δ := δ) f) := HasExt.standard _

variable (g : X ⟶ Y) (hg : g ≫ fY = f)

abbrev restriction : ModuleSheaf (p := p) (J := J) (δ := δ) fY ⥤ ModuleSheaf (p := p) (J := J) (δ := δ) f :=
  (BigCrystallineSite.postcompose g hg).sheafPushforwardContinuous (ModuleCat.{u + 1} (Coeff (B := B)))
    BigCrystallineSite.Object.topology BigCrystallineSite.Object.topology

instance restriction_additive : (restriction (p := p) (J := J) (δ := δ) g hg).Additive where
  map_add := by intros; rfl

instance restriction_linear : (restriction (p := p) (J := J) (δ := δ) g hg).Linear (Coeff (B := B)) where
  map_smul := by intros; rfl

instance restriction_leftAdjoint : (restriction (p := p) (J := J) (δ := δ) g hg).IsLeftAdjoint :=
  ((BigCrystallineSite.postcompose g hg).sheafAdjunctionCocontinuous (ModuleCat.{u + 1} (Coeff (B := B)))
    BigCrystallineSite.Object.topology BigCrystallineSite.Object.topology).isLeftAdjoint

instance restriction_preservesFiniteLimits :
    PreservesFiniteLimits (restriction (p := p) (J := J) (δ := δ) g hg) := by infer_instance

instance restriction_preservesFiniteColimits :
    PreservesFiniteColimits (restriction (p := p) (J := J) (δ := δ) g hg) := by infer_instance

/-- The linear map on Ext induced by the proved exact restriction functor. -/
def mapExt (F G : ModuleSheaf (p := p) (J := J) (δ := δ) fY) (n : ℕ) :
    Abelian.Ext.{u + 2} F G n →ₗ[Coeff (B := B)]
      Abelian.Ext.{u + 2} ((restriction g hg).obj F) ((restriction g hg).obj G) n :=
  (restriction g hg).mapExtLinearMap (Coeff (B := B)) F G n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction
