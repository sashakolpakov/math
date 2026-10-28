import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SliceImage
import Mathlib.CategoryTheory.Limits.FullSubcategory

/-! # Products -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Products

noncomputable section

/-!
# IntegralComparison: actual crystalline products remain in each bounded level
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u v w

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n : ℕ)

instance closedUnderNonemptyLimits (T : Type v) [Category.{w} T] [Nonempty T] :
    (Site.property (p := p) (J := J) (δ := δ) f n).IsClosedUnderLimitsOfShape T where
  limitsOfShape_le := by
    rintro U ⟨c⟩
    let t := Classical.arbitrary T
    exact Site.property_of_hom f n (c.π.app t) (c.prop_diag_obj t)

variable [Fact p.Prime] [IsSeparated f]

instance hasBinaryProducts : HasBinaryProducts (Site.Objects (p := p) (J := J) (δ := δ) f n) := by
  infer_instance

instance inclusion_preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) (Site.inclusion (p := p) (J := J) (δ := δ) f n) := by
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Products
