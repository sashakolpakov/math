import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ExtensionComponents

/-! # Extension Faces -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ExtensionFaces

noncomputable section

/-! The two paths around a relative Čech face use the same actual
open restriction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive _root_.TopologicalSpace Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Indices OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Intersections
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ExtensionComponents

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem projection_map_congr {C : Type*} [Category C]
    [∀ (A B : C), Subsingleton (A ⟶ B)]
    {D : Type*} [Category D] {ι : Type*} (P : C ⥤ D) (T : ι → C)
    [HasProduct (fun i => P.obj (T i))]
    {a b : ι} (h : a = b) {W : C} (f : T a ⟶ W) (g : T b ⟶ W) :
    Pi.π (fun i => P.obj (T i)) a ≫ P.map f =
      Pi.π (fun i => P.obj (T i)) b ≫ P.map g := by
  subst b
  exact congrArg (fun r => Pi.π (fun i => P.obj (T i)) a ≫ P.map r)
    (Subsingleton.elim f g)

universe u v
variable {X : TopCat.{u}} (U : Opens X)
  {ι : Type u} [LinearOrder ι] (V : ι → Opens X)
  {D : Type v} [Category D] [Preadditive D] [HasProducts.{u} D]
  (P : X.Presheaf D)

omit [Preadditive D] in
theorem face_coordinate {n : ℕ} (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 2))
    (h : a.val 0 = ⊥) (j : Fin (n + 1)) :
    (ExtensionComponents.sourceProjection U V P ((Indices.tail a h).delete j) ≫
      (Intersections.presheaf U P).map ((AugmentedOrdered.Cech.face V n j).φ (Indices.tail a h)).op) ≫
        P.map (Intersections.intersectionHom U V a h).op =
    (ExtensionComponents.sourceProjection U V P (Indices.tail (a.delete j.succ) (Indices.delete_succ_bot a h j)) ≫
      P.map (Intersections.intersectionHom U V (a.delete j.succ) (Indices.delete_succ_bot a h j)).op) ≫
        P.map ((AugmentedOrdered.Cech.face (Intersections.cover U V) (n + 1) j.succ).φ a).op := by
  change (Pi.π (fun b : AugmentedOrdered.Cech.Index ι n => P.obj (op (U ⊓ (AugmentedOrdered.Cech.formal V n).obj b)))
      ((Indices.tail a h).delete j) ≫
        P.map ((Intersections.intersect U).map ((AugmentedOrdered.Cech.face V n j).φ (Indices.tail a h))).op) ≫
          P.map (Intersections.intersectionHom U V a h).op =
    (Pi.π (fun b : AugmentedOrdered.Cech.Index ι n => P.obj (op (U ⊓ (AugmentedOrdered.Cech.formal V n).obj b)))
      (Indices.tail (a.delete j.succ) (Indices.delete_succ_bot a h j)) ≫
        P.map (Intersections.intersectionHom U V (a.delete j.succ) (Indices.delete_succ_bot a h j)).op) ≫
          P.map ((AugmentedOrdered.Cech.face (Intersections.cover U V) (n + 1) j.succ).φ a).op
  simp only [Category.assoc, ← P.map_comp]
  exact projection_map_congr P (fun b : AugmentedOrdered.Cech.Index ι n => op (U ⊓ (AugmentedOrdered.Cech.formal V n).obj b))
    (Indices.tail_delete_succ a h j).symm _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ExtensionFaces
