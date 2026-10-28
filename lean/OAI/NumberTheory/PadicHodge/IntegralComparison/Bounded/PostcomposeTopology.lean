import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeLifts
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeSieves
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Cocontinuous

/-! # Postcompose Topology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology

noncomputable section

/-!
# IntegralComparison: native bounded crystalline postcomposition is continuous and cocontinuous
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)

local notation "QX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n
local notation "QY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) fY n
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) g hg
local notation "F₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "JX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) f n
local notation "JY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) fY n

theorem coverPreserving : CoverPreserving JX JY F₀ where
  cover_preserve {U S} hS := by
    apply Functor.mem_restrictedTopology_of_functorPushforward_mem
    rw [PostcomposeSieves.pushforward_comp]
    exact (CoverPreserving.of_isContinuous F BigCrystallineSite.Object.topology
      BigCrystallineSite.Object.topology).cover_preserve
        ((CoverPreserving.of_isContinuous QX JX BigCrystallineSite.Object.topology).cover_preserve hS)

instance continuous : (F₀).IsContinuous JX JY :=
  Functor.isContinuous_of_coverPreserving
    ((PostcomposeLifts.incomingLifts g hg n).compatiblePreserving JY) (coverPreserving g hg n)

instance cocontinuous : (F₀).IsCocontinuous JX JY where
  cover_lift {U S} hS := by
    apply Functor.mem_restrictedTopology_of_functorPushforward_mem
    rw [PostcomposeSieves.pushforward_pullback]
    exact (F).cover_lift BigCrystallineSite.Object.topology BigCrystallineSite.Object.topology
      ((CoverPreserving.of_isContinuous QY JY BigCrystallineSite.Object.topology).cover_preserve hS)

abbrev restriction : BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fY n ⥤
    BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n :=
  (F₀).sheafPushforwardContinuous (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) JX JY

instance restriction_additive : (restriction (p := p) (J := J) (δ := δ) g hg n).Additive where
  map_add := by intros; rfl

instance restriction_linear : (restriction (p := p) (J := J) (δ := δ) g hg n).Linear (Crystalline.ExactRestriction.Coeff (B := B)) where
  map_smul := by intros; rfl

instance restriction_leftAdjoint : (restriction (p := p) (J := J) (δ := δ) g hg n).IsLeftAdjoint :=
  ((F₀).sheafAdjunctionCocontinuous (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) JX JY).isLeftAdjoint

instance restriction_preservesFiniteLimits :
    PreservesFiniteLimits (restriction (p := p) (J := J) (δ := δ) g hg n) := by infer_instance

instance restriction_preservesFiniteColimits :
    PreservesFiniteColimits (restriction (p := p) (J := J) (δ := δ) g hg n) := by infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology
