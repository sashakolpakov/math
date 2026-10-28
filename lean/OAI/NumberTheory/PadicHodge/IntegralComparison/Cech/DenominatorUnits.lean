import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechCoordinates
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! # Denominator Units -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DenominatorUnits

noncomputable section

/-! Canonical units and denominator cancellation on the actual ordered
Čech intersections. No choice of inverse or representative is imposed
on a restriction map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechCoordinates

variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C) (P : Cᵒᵖ ⥤ CommRingCat.{u})
  (R : Type u) [CommRing R]
  (α : (Functor.const Cᵒᵖ).obj (CommRingCat.of R) ⟶ P)
  (s : ι → R) (hs : ∀ i, IsUnit ((α.app (op (U i))) (s i)))

def ring {q : ℕ} (a : AugmentedOrdered.Cech.Index ι q) := P.obj (op ((AugmentedOrdered.Cech.formal U q).obj a))
instance {q : ℕ} (a : AugmentedOrdered.Cech.Index ι q) : CommRing (ring U P a) := inferInstanceAs (CommRing (P.obj _))

abbrev scalar {q : ℕ} (a : AugmentedOrdered.Cech.Index ι q) : R →+* ring U P a := (α.app _).hom

def coordinateUnit {q : ℕ} (a : AugmentedOrdered.Cech.Index ι q) (j : Fin q) : (ring U P a)ˣ :=
  (hs (a.val j)).unit.map (P.map (Pi.π (fun i : Fin q => U (a.val i)) j).op).hom.toMonoidHom

omit [HasFiniteProducts C] in
theorem scalar_natural {c d : C} (f : c ⟶ d) (r : R) :
    P.map f.op (α.app (op d) r) = α.app (op c) r := by
  have h := ConcreteCategory.congr_hom (α.naturality f.op) r
  exact h.symm

theorem coordinateUnit_val {q : ℕ} (a : AugmentedOrdered.Cech.Index ι q) (j : Fin q) :
    ((coordinateUnit U P R α s hs a j : (ring U P a)ˣ) : ring U P a) = scalar U P R α a (s (a.val j)) := by
  change P.map (Pi.π (fun i : Fin q => U (a.val i)) j).op ((hs (a.val j)).unit.val) = _
  rw [IsUnit.unit_spec]
  exact scalar_natural P R α _ _

def denominator {q : ℕ} (a : AugmentedOrdered.Cech.Index ι q) : (ring U P a)ˣ := ∏ j, coordinateUnit U P R α s hs a j

abbrev restriction {q : ℕ} (a : AugmentedOrdered.Cech.Index ι (q + 1)) (k : Fin (q + 1)) :
    ring U P (a.delete k) →+* ring U P a := (P.map ((AugmentedOrdered.Cech.face U q k).φ a).op).hom

theorem coordinateUnit_restriction {q : ℕ} (a : AugmentedOrdered.Cech.Index ι (q + 1)) (k : Fin (q + 1)) (j : Fin q) :
    (coordinateUnit U P R α s hs (a.delete k) j).map (restriction U P a k).toMonoidHom =
      coordinateUnit U P R α s hs a (k.succAbove j) := by
  apply Units.ext
  simp only [Units.coe_map, coordinateUnit_val]
  exact scalar_natural P R α _ _

theorem denominator_delete {q : ℕ} (a : AugmentedOrdered.Cech.Index ι (q + 1)) (k : Fin (q + 1)) :
    denominator U P R α s hs a = coordinateUnit U P R α s hs a k *
      (denominator U P R α s hs (a.delete k)).map (restriction U P a k).toMonoidHom := by
  unfold denominator
  rw [map_prod]
  simp_rw [coordinateUnit_restriction]
  exact Fin.prod_univ_succAbove (coordinateUnit U P R α s hs a) k

theorem cancellation {q : ℕ} (a : AugmentedOrdered.Cech.Index ι (q + 1)) (k : Fin (q + 1)) :
    scalar U P R α a (s (a.val k)) * (↑((denominator U P R α s hs a)⁻¹) : ring U P a) =
      restriction U P a k (↑((denominator U P R α s hs (a.delete k))⁻¹)) := by
  have h : coordinateUnit U P R α s hs a k * (denominator U P R α s hs a)⁻¹ =
      ((denominator U P R α s hs (a.delete k))⁻¹).map (restriction U P a k).toMonoidHom := by
    rw [denominator_delete U P R α s hs a k]
    simp [mul_inv_rev]
  have hval := congrArg Units.val h
  change _ * _ = restriction U P a k _ at hval
  rw [coordinateUnit_val] at hval
  exact hval

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DenominatorUnits
