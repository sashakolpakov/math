import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CechTopResidue

/-! # Reciprocal Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.ReciprocalTransport

noncomputable section

/-! The actual full-intersection reciprocal transports to the inverse
product of any units with the prescribed parameter values. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DenominatorUnits OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {m : ℕ} (U : ULift.{u} (Fin m) → C)
  (t : Fin m → R) (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))
  (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) m)
  {Q : Type v} [CommRing Q]
  (ρ : P.obj (op ((AugmentedOrdered.Cech.formal U m).obj a)) →+* Q) (units : Fin m → Qˣ)
  (hunits : ∀ j, ρ (algebraMap R (P.obj (op ((AugmentedOrdered.Cech.formal U m).obj a))) (t j)) = (units j : Q))

include hunits in
theorem coordinateUnit_map (j : Fin m) :
    (Cech.DenominatorUnits.coordinateUnit U (Fractions.rings R P) R (Fractions.scalars R P) (fun i => t i.down) ht a j).map
      ρ.toMonoidHom = units j := by
  apply Units.ext
  change ρ (Cech.DenominatorUnits.coordinateUnit U (Fractions.rings R P) R (Fractions.scalars R P) (fun i => t i.down) ht a j).val = _
  rw [Cech.DenominatorUnits.coordinateUnit_val]
  change ρ (algebraMap R (P.obj (op ((AugmentedOrdered.Cech.formal U m).obj a))) (t (a.val j).down)) = _
  rw [congrFun (Koszul.CechTopResidue.tuple_down a) j]
  exact hunits j

include hunits in
theorem denominator_map :
    (Cech.DenominatorUnits.denominator U (Fractions.rings R P) R (Fractions.scalars R P) (fun i => t i.down) ht a).map ρ.toMonoidHom =
      ∏ j, units j := by
  simp only [Cech.DenominatorUnits.denominator, map_prod]
  exact Finset.prod_congr rfl (fun j _ => coordinateUnit_map R P U t ht a ρ units hunits j)

include hunits in
theorem reciprocal_map :
    ρ (Fractions.reciprocal R P U t ht a) = ((∏ j, units j)⁻¹ : Qˣ).val := by
  change (((Cech.DenominatorUnits.denominator U (Fractions.rings R P) R (Fractions.scalars R P) (fun i => t i.down) ht a)⁻¹).map
    ρ.toMonoidHom).val = _
  rw [map_inv, denominator_map R P U t ht a ρ units hunits]

theorem top_reciprocal_map (hm : Fintype.card (ULift.{u} (Fin m)) = m)
    (ρ : P.obj (op (AugmentedOrdered.CechCoordinates.topObject U m hm)) →+* Q) (units : Fin m → Qˣ)
    (hunits : ∀ j, ρ (algebraMap R (P.obj (op (AugmentedOrdered.CechCoordinates.topObject U m hm))) (t j)) = (units j : Q)) :
    ρ (Fractions.reciprocal R P U t ht (AugmentedOrdered.CechCoordinates.topIndex m hm)) =
      ((∏ j, units j)⁻¹ : Qˣ).val :=
  reciprocal_map R P U t ht (AugmentedOrdered.CechCoordinates.topIndex m hm) ρ units hunits

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.ReciprocalTransport
