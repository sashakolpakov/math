import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Intersections

/-! # Extension Components -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ExtensionComponents

noncomputable section

/-! Extension of local relative Čech cochains by zero on tuples which
do not contain the distinguished chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive _root_.TopologicalSpace Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Indices OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Intersections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {X : TopCat.{u}} (U : Opens X)
  {ι : Type u} [LinearOrder ι] (V : ι → Opens X)
  {D : Type v} [Category D] [Preadditive D] [HasProducts.{u} D]
  (P : X.Presheaf D)

def sourceProjection {n : ℕ} (a : AugmentedOrdered.Cech.Index ι n) :
    AugmentedOrdered.Cech.object V (Intersections.presheaf U P) n ⟶ P.obj (op (U ⊓ (AugmentedOrdered.Cech.formal V n).obj a)) :=
  Pi.π (fun b : AugmentedOrdered.Cech.Index ι n => (Intersections.presheaf U P).obj (op ((AugmentedOrdered.Cech.formal V n).obj b))) a

def targetProjection {n : ℕ} (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 1)) :
    AugmentedOrdered.Cech.object (Intersections.cover U V) P (n + 1) ⟶ P.obj (op ((AugmentedOrdered.Cech.formal (Intersections.cover U V) (n + 1)).obj a)) :=
  Pi.π (fun b : AugmentedOrdered.Cech.Index (WithBot ι) (n + 1) =>
    P.obj (op ((AugmentedOrdered.Cech.formal (Intersections.cover U V) (n + 1)).obj b))) a

def entry {n : ℕ} (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 1)) :
    AugmentedOrdered.Cech.object V (Intersections.presheaf U P) n ⟶ P.obj (op ((AugmentedOrdered.Cech.formal (Intersections.cover U V) (n + 1)).obj a)) := by
  classical
  exact if h : a.val 0 = ⊥ then
    (-1 : ℤ)^n • (sourceProjection U V P (Indices.tail a h) ≫ P.map (Intersections.intersectionHom U V a h).op)
  else 0

def component (n : ℕ) : AugmentedOrdered.Cech.object V (Intersections.presheaf U P) n ⟶ AugmentedOrdered.Cech.object (Intersections.cover U V) P (n + 1) :=
  Pi.lift (entry U V P)

theorem component_projection {n : ℕ} (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 1)) :
    component U V P n ≫ targetProjection U V P a = entry U V P a :=
  Pi.lift_comp_π _ a

theorem component_bot {n : ℕ} (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 1)) (h : a.val 0 = ⊥) :
    component U V P n ≫ targetProjection U V P a =
      (-1 : ℤ)^n • (sourceProjection U V P (Indices.tail a h) ≫
        P.map (Intersections.intersectionHom U V a h).op) := by
  rw [component_projection, entry, dite_eq_left h]

theorem component_ne_bot {n : ℕ} (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 1)) (h : a.val 0 ≠ ⊥) :
    component U V P n ≫ targetProjection U V P a = 0 := by
  rw [component_projection, entry, dite_eq_right h]

theorem differential_source {n : ℕ} (a : AugmentedOrdered.Cech.Index ι (n + 1)) :
    AugmentedOrdered.Cech.differential V (Intersections.presheaf U P) n ≫ sourceProjection U V P a =
      ∑ j : Fin (n + 1), (-1 : ℤ)^j.val •
        (sourceProjection U V P (a.delete j) ≫
          (Intersections.presheaf U P).map ((AugmentedOrdered.Cech.face V n j).φ a).op) :=
  AugmentedOrdered.CechCoordinates.differential_comp_pi V (Intersections.presheaf U P) n a

theorem differential_target {n : ℕ} (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 2)) :
    AugmentedOrdered.Cech.differential (Intersections.cover U V) P (n + 1) ≫ targetProjection U V P a =
      ∑ j : Fin (n + 2), (-1 : ℤ)^j.val •
        (targetProjection U V P (a.delete j) ≫ P.map ((AugmentedOrdered.Cech.face (Intersections.cover U V) (n + 1) j).φ a).op) :=
  AugmentedOrdered.CechCoordinates.differential_comp_pi (Intersections.cover U V) P (n + 1) a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ExtensionComponents
