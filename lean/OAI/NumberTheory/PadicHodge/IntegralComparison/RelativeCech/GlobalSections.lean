import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ExtensionNaturality

/-! # Global Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.GlobalSections

noncomputable section

/-! Relative extension recovers the ordinary global Čech augmentation
on sections which vanish on the complementary charts. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive _root_.TopologicalSpace Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Indices OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Intersections
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ExtensionComponents

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {X : TopCat.{u}} (U : Opens X)
  {ι : Type u} [LinearOrder ι] (V : ι → Opens X)
  {D : Type v} [Category D] [Preadditive D] [HasProducts.{u} D]
  (P : X.Presheaf D)

def relativeAugmentation : P.obj (op (⊤ : Opens X)) ⟶ AugmentedOrdered.Cech.object V (Intersections.presheaf U P) 0 :=
  Pi.lift fun a : AugmentedOrdered.Cech.Index ι 0 => P.map
    (homOfLE (le_top : U ⊓ (AugmentedOrdered.Cech.formal V 0).obj a ≤ ⊤)).op

def globalAugmentation : P.obj (op (⊤ : Opens X)) ⟶ AugmentedOrdered.Cech.object V P 1 :=
  Pi.lift fun a : AugmentedOrdered.Cech.Index ι 1 => P.map
    (homOfLE (le_top : (AugmentedOrdered.Cech.formal V 1).obj a ≤ ⊤)).op

omit [Preadditive D] in
theorem relativeAugmentation_projection (a : AugmentedOrdered.Cech.Index ι 0) :
    relativeAugmentation U V P ≫ ExtensionComponents.sourceProjection U V P a =
      P.map (homOfLE (le_top : U ⊓ (AugmentedOrdered.Cech.formal V 0).obj a ≤ ⊤)).op :=
  Pi.lift_comp_π _ a

omit [Preadditive D] in
theorem globalAugmentation_projection (a : AugmentedOrdered.Cech.Index (WithBot ι) 1) :
    globalAugmentation (Intersections.cover U V) P ≫ ExtensionComponents.targetProjection U V P a =
      P.map (homOfLE (le_top : (AugmentedOrdered.Cech.formal (Intersections.cover U V) 1).obj a ≤ ⊤)).op :=
  Pi.lift_comp_π _ a

theorem augmentation_bot (a : AugmentedOrdered.Cech.Index (WithBot ι) 1) (h : a.val 0 = ⊥) :
    (relativeAugmentation U V P ≫ ExtensionComponents.component U V P 0) ≫ ExtensionComponents.targetProjection U V P a =
      P.map (homOfLE (le_top : (AugmentedOrdered.Cech.formal (Intersections.cover U V) 1).obj a ≤ ⊤)).op := by
  rw [Category.assoc, ExtensionComponents.component_bot U V P a h, pow_zero, one_zsmul,
    ← Category.assoc, relativeAugmentation_projection, ← P.map_comp]
  congr 1

variable {M : D} (s : M ⟶ P.obj (op (⊤ : Opens X)))
  (hV : ∀ i, s ≫ P.map (homOfLE (le_top : V i ≤ ⊤)).op = 0)

include hV in
omit [HasProducts D] in
theorem complementary_zero (a : AugmentedOrdered.Cech.Index (WithBot ι) 1) (h : a.val 0 ≠ ⊥) :
    s ≫ P.map (homOfLE (le_top : (AugmentedOrdered.Cech.formal (Intersections.cover U V) 1).obj a ≤ ⊤)).op = 0 := by
  let i := (a.val 0).unbot h
  have hi : (AugmentedOrdered.Cech.formal (Intersections.cover U V) 1).obj a ≤ V i := by
    have ht := leOfHom (Pi.π (fun j : Fin 1 => Intersections.cover U V (a.val j)) 0)
    rw [← WithBot.coe_unbot (a.val 0) h, Intersections.cover_coe] at ht
    exact ht
  calc
    _ = (s ≫ P.map (homOfLE (le_top : V i ≤ ⊤)).op) ≫ P.map (homOfLE hi).op := by
      rw [Category.assoc, ← P.map_comp]
      congr 1
    _ = 0 := by rw [hV i, zero_comp]

include hV in
theorem augmentation :
    (s ≫ relativeAugmentation U V P) ≫ ExtensionComponents.component U V P 0 =
      s ≫ globalAugmentation (Intersections.cover U V) P := by
  classical
  apply Pi.hom_ext
  intro (a : AugmentedOrdered.Cech.Index (WithBot ι) 1)
  change _ ≫ ExtensionComponents.targetProjection U V P a = _ ≫ ExtensionComponents.targetProjection U V P a
  rw [Category.assoc s, Category.assoc s, Category.assoc s,
    globalAugmentation_projection]
  by_cases h : a.val 0 = ⊥
  · rw [augmentation_bot U V P a h]
  · rw [Category.assoc, ExtensionComponents.component_ne_bot U V P a h, comp_zero, comp_zero,
      complementary_zero U V P s hV a h]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.GlobalSections
