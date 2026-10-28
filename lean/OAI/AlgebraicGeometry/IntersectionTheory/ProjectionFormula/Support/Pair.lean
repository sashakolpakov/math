import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SimultaneousIncidenceCut
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.ProductSupport

/-! # Pair -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Pair

noncomputable section

/-! The actual scheme of pairs on two cycle supports is a
Noetherian finite-type scheme over the complex base. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W Z : IrreducibleCloseds X.carrier)

abbrev space : Scheme :=
  pullback (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap) (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ X.structureMap)

def base : space X W Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase :=
  pullback.fst _ _ ≫ CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap

def over : Over Foundations.Scheme.ProjectiveSpace.complexBase := Over.mk (base X W Z)

def first : over X W Z ⟶ X.toOver :=
  Over.homMk (pullback.fst _ _ ≫ CycleClass.Geometric.GenericPoint.reducedSupportι W) (by simp only [Category.assoc]; rfl)

def second : over X W Z ⟶ X.toOver :=
  Over.homMk (pullback.snd _ _ ≫ CycleClass.Geometric.GenericPoint.reducedSupportι Z) (by
    change (pullback.snd _ _ ≫ CycleClass.Geometric.GenericPoint.reducedSupportι Z) ≫ X.structureMap =
      pullback.fst _ _ ≫ CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap
    rw [Category.assoc]
    exact pullback.condition.symm)

instance noetherian : IsNoetherian (space X W Z) where

instance finiteType : LocallyOfFiniteType (base X W Z) := by
  unfold base
  infer_instance

instance over_noetherian : NoetherianSpace (over X W Z).left :=
  inferInstanceAs (NoetherianSpace (space X W Z))

instance over_finiteType : LocallyOfFiniteType (over X W Z).hom :=
  inferInstanceAs (LocallyOfFiniteType (base X W Z))

theorem dimension (C : IrreducibleCloseds (space X W Z)) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension C (base X W Z) ≤
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap + Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.structureMap :=
  ProductSupportDimension.bound (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap)
    (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ X.structureMap) C

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Pair
