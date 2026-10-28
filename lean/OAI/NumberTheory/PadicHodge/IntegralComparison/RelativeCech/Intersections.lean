import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Indices
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Projection
import Mathlib.Topology.Category.TopCat.Limits.Products

/-! # Intersections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Intersections

noncomputable section

/-! The distinguished-chart intersections in a relative ordered Čech
cover are precisely the intersections used by the local augmented complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Indices

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {X : TopCat.{u}} (U : Opens X)
  {ι : Type u} [LinearOrder ι] (V : ι → Opens X)

def cover : WithBot ι → Opens X := fun i => Option.elim i U V

def intersect : Opens X ⥤ Opens X :=
  OrderHom.toFunctor { toFun := fun W => U ⊓ W, monotone' := fun _ _ h => inf_le_inf_left U h }

def presheaf {D : Type v} [Category D] (P : X.Presheaf D) : X.Presheaf D :=
  (intersect U).op ⋙ P

omit [LinearOrder ι] in
theorem cover_bot : cover U V ⊥ = U := rfl

omit [LinearOrder ι] in
theorem cover_coe (i : ι) : cover U V (i : WithBot ι) = V i := rfl

theorem cover_tail {n : ℕ} (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 1))
    (h : a.val 0 = ⊥) (j : Fin n) :
    cover U V (a.val j.succ) = V ((Indices.tail a h).val j) := by
  rw [← Indices.coe_tail a h j]
  rfl

def intersectionHom {n : ℕ} (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 1))
    (h : a.val 0 = ⊥) :
    (AugmentedOrdered.Cech.formal (cover U V) (n + 1)).obj a ⟶
      U ⊓ (AugmentedOrdered.Cech.formal V n).obj (Indices.tail a h) := by
  apply homOfLE
  apply le_inf
  · change (∏ᶜ fun j : Fin (n + 1) => cover U V (a.val j)) ≤ U
    have hp := leOfHom (Pi.π (fun j : Fin (n + 1) => cover U V (a.val j)) 0)
    exact hp.trans (by rw [h, cover_bot])
  · apply leOfHom
    apply Pi.lift
    intro j
    have hp := leOfHom (Pi.π (fun j : Fin (n + 1) => cover U V (a.val j)) j.succ)
    exact homOfLE ((cover_tail U V a h j) ▸ hp)

def intersectionInv {n : ℕ} (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 1))
    (h : a.val 0 = ⊥) :
    U ⊓ (AugmentedOrdered.Cech.formal V n).obj (Indices.tail a h) ⟶
      (AugmentedOrdered.Cech.formal (cover U V) (n + 1)).obj a := by
  apply Pi.lift
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · apply homOfLE
    simpa only [h, cover_bot] using
      (inf_le_left : U ⊓ (AugmentedOrdered.Cech.formal V n).obj (Indices.tail a h) ≤ U)
  · apply homOfLE
    rw [cover_tail U V a h i]
    exact inf_le_right.trans (leOfHom (Pi.π (fun i : Fin n => V ((Indices.tail a h).val i)) i))

def intersectionIso {n : ℕ} (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 1))
    (h : a.val 0 = ⊥) :
    (AugmentedOrdered.Cech.formal (cover U V) (n + 1)).obj a ≅
      U ⊓ (AugmentedOrdered.Cech.formal V n).obj (Indices.tail a h) where
  hom := intersectionHom U V a h
  inv := intersectionInv U V a h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Intersections
