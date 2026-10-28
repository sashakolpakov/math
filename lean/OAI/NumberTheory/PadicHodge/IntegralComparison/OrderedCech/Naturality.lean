import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Homotopy
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Functor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TupleRestrictionNaturality

/-! # Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Naturality

noncomputable section

/-! Projection and signed-sorting inclusion are natural in coefficient
presheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite

universe u v
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {D : Type v} [Category D] [Preadditive D] [HasProducts.{u} D]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {P Q : Cᵒᵖ ⥤ D} (a : P ⟶ Q)

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TupleRestrictionNaturality.Functor OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Functor.Projection

theorem projection : Cech.TupleRestrictionNaturality.Functor.coefficientMap U a ≫ Projection.map U Q =
    Projection.map U P ≫ Functor.Projection.complexMap U a := by
  apply HomologicalComplex.hom_ext
  intro n
  apply Pi.hom_ext
  intro (i : Projection.Index (ι := ι) n)
  change ((Cech.TupleRestrictionNaturality.Functor.coefficientMap U a).f n ≫ Projection.mapF U Q n) ≫
      Projection.projection U Q n i =
    (Projection.mapF U P n ≫ AugmentedOrdered.CechFunctor.objectMap U a (n + 1)) ≫
      Projection.projection U Q n i
  have h := AugmentedOrdered.CechCoordinates.objectMap_comp_pi U P a (n + 1) i
  change AugmentedOrdered.CechFunctor.objectMap U a (n + 1) ≫
    Projection.projection U Q n i =
    Projection.projection U P n i ≫ a.app _ at h
  rw [Category.assoc, Projection.mapF_projection, Cech.TupleRestrictionNaturality.Functor.coefficientMap_projection,
    Category.assoc, h, ← Category.assoc, Projection.mapF_projection]

theorem inclusion : Functor.Projection.complexMap U a ≫ Retraction.inclusion U Q =
    Retraction.inclusion U P ≫ Cech.TupleRestrictionNaturality.Functor.coefficientMap U a := by
  apply HomologicalComplex.hom_ext
  intro n
  apply (cancel_epi (Projection.mapF U P n)).mp
  change Projection.mapF U P n ≫ (AugmentedOrdered.CechFunctor.objectMap U a (n + 1) ≫
      Retraction.inclusionF U Q n) =
    Projection.mapF U P n ≫ (Retraction.inclusionF U P n ≫ (Cech.TupleRestrictionNaturality.Functor.coefficientMap U a).f n)
  have h := congrArg (fun z => z.f n) (projection U a)
  change (Cech.TupleRestrictionNaturality.Functor.coefficientMap U a).f n ≫ Projection.mapF U Q n =
    Projection.mapF U P n ≫ AugmentedOrdered.CechFunctor.objectMap U a (n + 1) at h
  rw [← Category.assoc, ← h, Category.assoc, Retraction.mapF_inclusionF,
    ← Category.assoc, Retraction.mapF_inclusionF]
  exact Cech.TupleRestrictionNaturality.Functor.map_naturality U a _ _

def projectionTransformation : NonemptyCechNerve.complexFunctor U (A := D) ⟶ Functor.Projection.functor U (D := D) where
  app P := Projection.map U P
  naturality _ _ a := projection U a

def inclusionTransformation : Functor.Projection.functor U (D := D) ⟶ NonemptyCechNerve.complexFunctor U (A := D) where
  app P := Retraction.inclusion U P
  naturality _ _ a := inclusion U a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Naturality
