import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CechFractions
import Mathlib.Order.Preorder.Finite

/-! # Cech Top Residue -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CechTopResidue

noncomputable section

/-! The ordered top Koszul generator maps to the literal reciprocal
product on the unique full Čech intersection, with coefficient one. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DenominatorUnits OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CechFractions

variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {m : ℕ} (U : ULift.{u} (Fin m) → C) (P : Cᵒᵖ ⥤ CommRingCat.{u})
  (R : Type u) [CommRing R]
  (α : (Functor.const Cᵒᵖ).obj (CommRingCat.of R) ⟶ P)
  (s : Fin m → R) (hs : ∀ i, IsUnit ((α.app (op (U i))) (s i.down)))

def fullIndex : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) m := ⟨ULift.up, fun _ _ h => h⟩

theorem tuple_down (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) m) :
    (fun j => (a.val j).down) = id :=
  StrictMono.eq_id (fun _ _ h => a.property h)

def topFunctional : Module.Dual R (⋀[R]^m (Fin m → R)) :=
  TopExteriorCoordinates.coordinate (Pi.basisFun R (Fin m))

theorem topFunctional_one : topFunctional R (m := m)
    (exteriorPower.ιMulti R m (Pi.basisFun R (Fin m))) = 1 :=
  TopExteriorCoordinates.coordinate_generator _

theorem coordinate_top (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) m) :
    CechFractions.coordinate U P R α s hs m a (topFunctional R) =
      (↑((Cech.DenominatorUnits.denominator U P R α (fun i => s i.down) hs a)⁻¹) : Cech.DenominatorUnits.ring U P a) := by
  have hv : (fun j => (Pi.basisFun R (Fin m)) (a.val j).down) = Pi.basisFun R (Fin m) := by
    funext j
    exact congrArg (Pi.basisFun R (Fin m)) (congrFun (tuple_down a) j)
  change Cech.DenominatorUnits.scalar U P R α a ((topFunctional R) (exteriorPower.ιMulti R m _)) * _ = _
  rw [hv, topFunctional_one, map_one, one_mul]

theorem map_top (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) m) :
    Pi.π (fun b : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) m =>
      (CechFractions.coefficient P).obj (op ((AugmentedOrdered.Cech.formal U m).obj b))) a
      ((CechFractions.map U P R α s hs).f m (topFunctional R)) =
      (↑((Cech.DenominatorUnits.denominator U P R α (fun i => s i.down) hs a)⁻¹) : Cech.DenominatorUnits.ring U P a) := by
  have h := ConcreteCategory.congr_hom (CechFractions.map_comp_pi U P R α s hs m a) (topFunctional R)
  exact h.trans (coordinate_top U P R α s hs a)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CechTopResidue
