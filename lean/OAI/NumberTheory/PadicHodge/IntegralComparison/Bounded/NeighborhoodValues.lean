import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Neighborhoods
import OAI.NumberTheory.PadicHodge.IntegralComparison.NeighborhoodColimit

/-! # Neighborhood Values -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.NeighborhoodValues

noncomputable section

/-!
# IntegralComparison: exact neighborhood-colimit values for the original bounded crystalline coefficients
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (T : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n)

local notation "V" => ModuleCat (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B))
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionPresheaf.property (p := p) (J := J) (δ := δ) fY n

instance colimits : HasColimitsOfShape (BoundedCrystalline.Neighborhoods.Objects fY n T)ᵒᵖ
    (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) := by infer_instance

instance exactColimits : HasExactColimitsOfShape (BoundedCrystalline.Neighborhoods.Objects fY n T)ᵒᵖ
    (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) := by
  let : AB5OfSize.{u, u} (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) := AB5OfSize_shrink.{u, u, u + 1, u + 1} _
  infer_instance

def functor : (Y.Opensᵒᵖ ⥤ ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) ⥤
    ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)) := NeighborhoodColimit.functor P T

instance preservesMonomorphisms : (functor fY n T).PreservesMonomorphisms :=
  NeighborhoodColimit.preservesMonomorphisms P T

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.NeighborhoodValues
