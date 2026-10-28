import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleMapCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.AmbientTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Refinement
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # Single Functor Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.SingleFunctorCoordinates

noncomputable section

/-! Each original Čech comparison factor commutes with the canonical
single-degree total coordinates. The coefficient maps below are the
literal ambient isomorphism, refinements, and relative extension. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleTotal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X : TopCat.{u}} {D : Type v} [Category D] [Abelian D]
  [HasProducts.{u} D] [HasCoproducts.{0} D]
  (P : (Opens X)ᵒᵖ ⥤ D) (c n : ℕ)

section Ambient
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X) {ι : Type u} [LinearOrder ι] (W : ι → C)
  [∀ (k : ℕ) (a : Fin (k+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) F]

abbrev localFunctor : ((Opens X)ᵒᵖ ⥤ D) ⥤ CochainComplex D ℕ :=
  AugmentedCech.AmbientTotal.restriction F ⋙ AugmentedOrdered.CechFunctor.functor W

theorem ambient :
    homologyMap (AugmentedCech.AmbientTotal.totalIso F W
      ((single ((Opens X)ᵒᵖ ⥤ D) (.up ℕ) c).obj P)).hom (n+c) ≫
        (IntegralComparison.Functor.SingleTotal.homologyIso (RelativeCech.Total.localFunctor (F.obj (⊤_ C)) (F.obj ∘ W)) P c n).hom =
      (IntegralComparison.Functor.SingleTotal.homologyIso (localFunctor F W) P c n).hom ≫
        homologyMap (AugmentedCech.AmbientCoordinates.iso F W P).hom n :=
  IntegralComparison.Functor.SingleMapCoordinates.naturality (localFunctor F W)
    (RelativeCech.Total.localFunctor (F.obj (⊤_ C)) (F.obj ∘ W))
    (AugmentedCech.AmbientCoordinates.functorIso F W).hom P c n
end Ambient

variable (A : Opens X) {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (U : ι → Opens X) (V : κ → Opens X)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)

theorem relative :
    RelativeCech.Refinement.homology A U V r
      ((single ((Opens X)ᵒᵖ ⥤ D) (.up ℕ) c).obj P) (n+c) ≫
        (IntegralComparison.Functor.SingleTotal.homologyIso (RelativeCech.Total.localFunctor A V) P c n).hom =
      (IntegralComparison.Functor.SingleTotal.homologyIso (RelativeCech.Total.localFunctor A U) P c n).hom ≫
        homologyMap (AugmentedOrdered.CechRefinement.map U V r
          ((RelativeCech.Intersections.intersect A).op ⋙ P)) n :=
  IntegralComparison.Functor.SingleMapCoordinates.naturality
    (RelativeCech.Total.localFunctor A U) (RelativeCech.Total.localFunctor A V)
    (Functor.whiskerLeft (RelativeCech.Refinement.restriction A)
      (AugmentedOrdered.CechRefinementTotal.transformation U V r)) P c n

theorem extension :
    homologyMap (RelativeCech.Total.map A U
      ((single ((Opens X)ᵒᵖ ⥤ D) (.up ℕ) c).obj P)) (n+c) ≫
        (IntegralComparison.Functor.SingleTotal.homologyIso (OrderedCech.Functor.Projection.functor (RelativeCech.Intersections.cover A U)) P c n).hom =
      (IntegralComparison.Functor.SingleTotal.homologyIso (RelativeCech.Total.localFunctor A U) P c n).hom ≫
        homologyMap ((RelativeCech.Total.comparison A U).app P) n :=
  IntegralComparison.Functor.SingleMapCoordinates.naturality (RelativeCech.Total.localFunctor A U)
    (OrderedCech.Functor.Projection.functor (RelativeCech.Intersections.cover A U))
    (RelativeCech.Total.comparison A U) P c n

theorem ordered :
    homologyMap (OrderedCech.Refinement.totalMap U V r
      ((single ((Opens X)ᵒᵖ ⥤ D) (.up ℕ) c).obj P)) (n+c) ≫
        (IntegralComparison.Functor.SingleTotal.homologyIso (OrderedCech.Functor.Projection.functor V) P c n).hom =
      (IntegralComparison.Functor.SingleTotal.homologyIso (OrderedCech.Functor.Projection.functor U) P c n).hom ≫
        homologyMap (OrderedCech.Refinement.map U V r P) n :=
  IntegralComparison.Functor.SingleMapCoordinates.naturality (OrderedCech.Functor.Projection.functor U)
    (OrderedCech.Functor.Projection.functor V) (OrderedCech.Refinement.transformation U V r) P c n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.SingleFunctorCoordinates
