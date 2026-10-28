import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CohomologyTransition
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.StructureCoordinates

/-! # Structure Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.StructureCoordinates

noncomputable section

/-! Original ambient-ring coordinates are unchanged by restriction to a lower bounded level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n m : ℕ) (hnm : n ≤ m)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm

theorem coordinates : Functor.whiskerLeft (G).op (Bounded.StructureCoordinates.presheafIso f m).hom ≫
    (Bounded.CohomologyTransition.structureIso f n m hnm).hom.hom =
      (Bounded.StructureCoordinates.presheafIso f n).hom := by
  apply NatTrans.ext
  funext U
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.StructureCoordinates
