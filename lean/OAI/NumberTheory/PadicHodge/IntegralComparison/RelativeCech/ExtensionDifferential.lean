import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ExtensionFaces

/-! # Extension Differential -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ExtensionDifferential

noncomputable section

/-! The relative extension includes the alternating sign forced by
placing the distinguished chart first in every ordered tuple. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive _root_.TopologicalSpace Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Indices OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Intersections
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ExtensionComponents OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ExtensionFaces

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {X : TopCat.{u}} (U : Opens X)
  {ι : Type u} [LinearOrder ι] (V : ι → Opens X)
  {D : Type v} [Category D] [Preadditive D] [HasProducts.{u} D]
  (P : X.Presheaf D)

def faceValue {n : ℕ} (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 2))
    (h : a.val 0 = ⊥) (j : Fin (n + 1)) :=
  (ExtensionComponents.sourceProjection U V P ((Indices.tail a h).delete j) ≫
    (Intersections.presheaf U P).map ((AugmentedOrdered.Cech.face V n j).φ (Indices.tail a h)).op) ≫
      P.map (Intersections.intersectionHom U V a h).op

theorem left_bot {n : ℕ} (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 2)) (h : a.val 0 = ⊥) :
    (ExtensionComponents.component U V P n ≫ AugmentedOrdered.Cech.differential (Intersections.cover U V) P (n + 1)) ≫
      ExtensionComponents.targetProjection U V P a =
        ∑ j : Fin (n + 1), (-1 : ℤ)^(j.val + 1) •
          ((-1 : ℤ)^n • faceValue U V P a h j) := by
  rw [Category.assoc, ExtensionComponents.differential_target, comp_sum, Fin.sum_univ_succ]
  have hz : ExtensionComponents.component U V P n ≫
      ((-1 : ℤ)^(0 : Fin (n + 2)).val •
        (ExtensionComponents.targetProjection U V P (a.delete 0) ≫
          P.map ((AugmentedOrdered.Cech.face (Intersections.cover U V) (n + 1) 0).φ a).op)) = 0 := by
    rw [comp_zsmul, ← Category.assoc,
      ExtensionComponents.component_ne_bot U V P (a.delete 0) (Indices.delete_zero_ne_bot a h), zero_comp, smul_zero]
  rw [hz, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  rw [comp_zsmul, ← Category.assoc,
    ExtensionComponents.component_bot U V P (a.delete j.succ) (Indices.delete_succ_bot a h j), zsmul_comp]
  rw [← ExtensionFaces.face_coordinate U V P a h j]
  rfl

theorem right_bot {n : ℕ} (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 2)) (h : a.val 0 = ⊥) :
    (AugmentedOrdered.Cech.differential V (Intersections.presheaf U P) n ≫ ExtensionComponents.component U V P (n + 1)) ≫
      ExtensionComponents.targetProjection U V P a =
        ∑ j : Fin (n + 1), (-1 : ℤ)^(n + 1) •
          ((-1 : ℤ)^j.val • faceValue U V P a h j) := by
  rw [Category.assoc, ExtensionComponents.component_bot U V P a h, comp_zsmul, ← Category.assoc,
    ExtensionComponents.differential_source, sum_comp, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [zsmul_comp]
  rfl

theorem left_ne_bot {n : ℕ} (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 2)) (h : a.val 0 ≠ ⊥) :
    (ExtensionComponents.component U V P n ≫ AugmentedOrdered.Cech.differential (Intersections.cover U V) P (n + 1)) ≫
      ExtensionComponents.targetProjection U V P a = 0 := by
  rw [Category.assoc, ExtensionComponents.differential_target, comp_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [comp_zsmul, ← Category.assoc,
    ExtensionComponents.component_ne_bot U V P (a.delete j) (Indices.delete_ne_bot a h j), zero_comp, smul_zero]

theorem comm (n : ℕ) :
    ExtensionComponents.component U V P n ≫ AugmentedOrdered.Cech.differential (Intersections.cover U V) P (n + 1) =
      AugmentedOrdered.Cech.differential V (Intersections.presheaf U P) n ≫ ExtensionComponents.component U V P (n + 1) := by
  classical
  apply Pi.hom_ext
  intro (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 2))
  change _ ≫ ExtensionComponents.targetProjection U V P a = _ ≫ ExtensionComponents.targetProjection U V P a
  by_cases h : a.val 0 = ⊥
  · rw [left_bot U V P a h, right_bot U V P a h]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul, smul_smul]
    congr 1
    simp only [pow_succ]
    ring
  · rw [left_ne_bot U V P a h, Category.assoc, ExtensionComponents.component_ne_bot U V P a h, comp_zero]

def map : AugmentedOrdered.Cech.complex V (Intersections.presheaf U P) ⟶
    OrderedCech.Projection.complex (Intersections.cover U V) P :=
  CochainComplex.ofHom (ExtensionComponents.component U V P) (fun n => by
    simpa only [AugmentedOrdered.Cech.complex, OrderedCech.Projection.complex,
      CochainComplex.of_d, OrderedCech.Projection.differential] using comm U V P n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ExtensionDifferential
