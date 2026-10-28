import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ExtensionDifferential
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Functor

/-! # Extension Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ExtensionNaturality

noncomputable section

/-! The relative Čech extension is natural in the coefficient presheaf,
so it also acts on the original complexes of sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive _root_.TopologicalSpace Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Indices OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Intersections
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ExtensionComponents

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {X : TopCat.{u}} (U : Opens X)
  {ι : Type u} [LinearOrder ι] (V : ι → Opens X)
  {D : Type v} [Category D] [Preadditive D] [HasProducts.{u} D]
  {P Q : X.Presheaf D} (f : P ⟶ Q)

omit [Preadditive D] in
theorem source_map_projection {n : ℕ} (a : AugmentedOrdered.Cech.Index ι n) :
    AugmentedOrdered.CechFunctor.objectMap V (Functor.whiskerLeft (Intersections.intersect U).op f) n ≫ ExtensionComponents.sourceProjection U V Q a =
      ExtensionComponents.sourceProjection U V P a ≫ f.app (op (U ⊓ (AugmentedOrdered.Cech.formal V n).obj a)) :=
  AugmentedOrdered.CechCoordinates.objectMap_comp_pi V (Intersections.presheaf U P) (Functor.whiskerLeft (Intersections.intersect U).op f) n a

omit [Preadditive D] in
theorem target_map_projection {n : ℕ} (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 1)) :
    AugmentedOrdered.CechFunctor.objectMap (Intersections.cover U V) f (n + 1) ≫ ExtensionComponents.targetProjection U V Q a =
      ExtensionComponents.targetProjection U V P a ≫ f.app (op ((AugmentedOrdered.Cech.formal (Intersections.cover U V) (n + 1)).obj a)) :=
  AugmentedOrdered.CechCoordinates.objectMap_comp_pi (Intersections.cover U V) P f (n + 1) a

theorem component_naturality (n : ℕ) :
    AugmentedOrdered.CechFunctor.objectMap V (Functor.whiskerLeft (Intersections.intersect U).op f) n ≫ ExtensionComponents.component U V Q n =
      ExtensionComponents.component U V P n ≫ AugmentedOrdered.CechFunctor.objectMap (Intersections.cover U V) f (n + 1) := by
  classical
  apply Pi.hom_ext
  intro (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 1))
  change _ ≫ ExtensionComponents.targetProjection U V Q a = _ ≫ ExtensionComponents.targetProjection U V Q a
  rw [Category.assoc, Category.assoc, target_map_projection]
  rw [← Category.assoc (ExtensionComponents.component U V P n) (ExtensionComponents.targetProjection U V P a)]
  by_cases h : a.val 0 = ⊥
  · rw [ExtensionComponents.component_bot U V Q a h, ExtensionComponents.component_bot U V P a h,
      comp_zsmul, zsmul_comp, ← Category.assoc, source_map_projection]
    simp only [Category.assoc]
    rw [f.naturality]
  · rw [ExtensionComponents.component_ne_bot U V Q a h, ExtensionComponents.component_ne_bot U V P a h, comp_zero, zero_comp]

def sourceFunctor : (X.Presheaf D) ⥤ CochainComplex D ℕ :=
  (Functor.whiskeringLeft _ _ D).obj (Intersections.intersect U).op ⋙ AugmentedOrdered.CechFunctor.functor V

def transformation : sourceFunctor U V (D := D) ⟶ OrderedCech.Functor.Projection.functor (Intersections.cover U V) where
  app P := ExtensionDifferential.map U V P
  naturality P Q f := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact component_naturality U V f n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ExtensionNaturality
