import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.PuncturedHomotopy
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.HomAcyclicProducts

/-! # Punctured Hom Rows -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.PuncturedHomRows

noncomputable section

/-! Positive supported Čech columns have exact Hom rows from the actual
point dual Koszul complex. One parameter is invertible on each genuine
intersection; its wedge nullhomotopy supplies the exactness. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.PuncturedHomotopy
open OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.HomAcyclicProducts
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (U : ULift.{u} (Fin m) → C)
  (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))

omit [HasFiniteProducts C] in
theorem rows_at (a : Cᵒᵖ) (j : Fin m)
    (hj : IsUnit (algebraMap R (P.obj a) (t j))) (p : ℕ) :
    Cochain.HomAcyclic.Rows (KoszulPartial.Components.source R s t) ((PuncturedHomotopy.coefficientAt R P s a).X p) := by
  let z : P.obj a := ↑(hj.unit⁻¹)
  have hz : algebraMap R (P.obj a) (t j) * z = 1 :=
    (congrArg (fun w : P.obj a => w * ↑(hj.unit⁻¹)) hj.unit_spec.symm).trans
      (Units.mul_inv hj.unit)
  exact Cochain.HomAcyclic.rows_of_scalar R (t j) (PuncturedHomotopy.sourceNull R s t j)
    ((PuncturedHomotopy.multiply R P s a z).f p)
    (congrArg (fun f => f.f p) (PuncturedHomotopy.multiply_inverse R P s a (t j) z hz))

include ht in
theorem positive (p q : ℕ) (hq : q ≠ 0) :
    Cochain.HomAcyclic.Rows (KoszulPartial.Components.source R s t) (((KoszulPartial.Components.target R P U s).X p).X q) := by
  apply Cochain.HomAcyclicProducts.rows_pi
  intro a
  let j : Fin q := ⟨0, Nat.pos_of_ne_zero hq⟩
  apply rows_at R P s t (op ((AugmentedOrdered.Cech.formal U q).obj a)) (a.val j).down
  let v := Cech.DenominatorUnits.coordinateUnit U (KoszulPartial.Fractions.rings R P) R (KoszulPartial.Fractions.scalars R P)
    (fun i => t i.down) ht a j
  exact ⟨v, Cech.DenominatorUnits.coordinateUnit_val U (KoszulPartial.Fractions.rings R P) R (KoszulPartial.Fractions.scalars R P)
    (fun i => t i.down) ht a j⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.PuncturedHomRows
