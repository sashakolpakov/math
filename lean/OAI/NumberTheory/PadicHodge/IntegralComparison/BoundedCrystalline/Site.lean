import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.Subsite
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

/-! # Site -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

noncomputable section

/-!
# IntegralComparison: bounded levels inside the original crystalline site

The level-n site is the full subcategory of actual original objects
killed by p^(n+1), with the native restricted topology. Incoming maps
preserve the bound, so its inclusion is continuous and cocontinuous.
Every original object belongs to some such level.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n : ℕ)

def property : ObjectProperty (BigCrystallineSite.Object p B J δ f) := fun U => (p : U.ring) ^ (n + 1) = 0

abbrev Objects := (property (p := p) (J := J) (δ := δ) f n).FullSubcategory

abbrev inclusion : Objects (p := p) (J := J) (δ := δ) f n ⥤ BigCrystallineSite.Object p B J δ f :=
  (property f n).ι

theorem property_of_hom {U V : BigCrystallineSite.Object p B J δ f} (α : U ⟶ V) (hV : property f n V) : property f n U := by
  change (p : U.ring) ^ (n + 1) = 0
  simpa only [map_pow, map_natCast, map_zero] using congrArg α.ringMap.toRingHom hV

theorem property_mono (m : ℕ) (hnm : n ≤ m) {U : BigCrystallineSite.Object p B J δ f} (hU : property f n U) : property f m U :=
  pow_eq_zero_of_le (Nat.add_le_add_right hnm 1) hU

omit n in
theorem exists_level (U : BigCrystallineSite.Object p B J δ f) : ∃ n, property f n U := by
  obtain ⟨n, hn⟩ := U.primeNilpotent
  exact ⟨n, pow_eq_zero_of_le (Nat.le_succ n) hn⟩

def topology : GrothendieckTopology (Objects (p := p) (J := J) (δ := δ) f n) :=
  (inclusion f n).restrictedTopology BigCrystallineSite.Object.topology

instance inclusion_continuous : (inclusion (p := p) (J := J) (δ := δ) f n).IsContinuous
    (topology f n) BigCrystallineSite.Object.topology :=
  Incoming.Subsite.continuous (property f n) (fun α => property_of_hom f n α) BigCrystallineSite.Object.topology

instance inclusion_cocontinuous : (inclusion (p := p) (J := J) (δ := δ) f n).IsCocontinuous
    (topology f n) BigCrystallineSite.Object.topology :=
  Incoming.Subsite.cocontinuous (property f n) (fun α => property_of_hom f n α) BigCrystallineSite.Object.topology

abbrev ModuleSheaf := Sheaf (topology (p := p) (J := J) (δ := δ) f n)
  (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))

abbrev restriction : Crystalline.ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f ⥤
    ModuleSheaf (p := p) (J := J) (δ := δ) f n :=
  (inclusion f n).sheafPushforwardContinuous (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))
    (topology f n) BigCrystallineSite.Object.topology

instance restriction_additive : (restriction (p := p) (J := J) (δ := δ) f n).Additive where
  map_add := by intros; rfl

instance restriction_leftAdjoint : (restriction (p := p) (J := J) (δ := δ) f n).IsLeftAdjoint :=
  ((inclusion f n).sheafAdjunctionCocontinuous (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))
    (topology f n) BigCrystallineSite.Object.topology).isLeftAdjoint

instance restriction_preservesFiniteLimits :
    PreservesFiniteLimits (restriction (p := p) (J := J) (δ := δ) f n) := by infer_instance

instance restriction_preservesFiniteColimits :
    PreservesFiniteColimits (restriction (p := p) (J := J) (δ := δ) f n) := by infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
