import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.PointClosureDimension
import OAI.AlgebraicGeometry.DivisorClass.Chern.SupportCodimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HorizontalFamilyFiber

/-! # Embedded Divisor Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.EmbeddedDivisorDimension

noncomputable section

/-! A nonzero divisor coefficient on an integral support has
point-closure dimension exactly one below that of the support. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (Z : Scheme) [AlgebraicGeometry.IsNoetherian Z]
  (f : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (C : IrreducibleCloseds Z)

theorem order (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme C).functionField)
    (y : CycleClass.Geometric.GenericPoint.reducedSupportScheme C) (hy : (CycleClass.Geometric.GenericPoint.reducedSupportScheme C).ord g y ≠ 0) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (CycleClass.Geometric.GenericPoint.reducedSupportι C y)) f + 1 =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension C f := by
  have hc : Order.coheight y = 1 := by
    by_contra hn
    exact hy (Scheme.ord_eq_zero_of_coheight_neq_one hn g)
  have hd := DivisorClass.Chern.SupportCodimension.Construction.pointClosure_dimension_add_one (CycleClass.Geometric.SupportFiniteType.supportStructureMap C f) y hc
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y) (CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ f) + 1 =
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension C f at hd
  rw [Closed.PointClosureDimension.dimension (CycleClass.Geometric.GenericPoint.reducedSupportι C) f y] at hd
  exact hd

theorem positive (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme C).functionField) (y : CycleClass.Geometric.GenericPoint.reducedSupportScheme C)
    (hy : PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme C) g) y ≠ 0) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (CycleClass.Geometric.GenericPoint.reducedSupportι C y)) f + 1 =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension C f := by
  apply order Z f C g y
  intro he
  apply hy
  rw [PositiveCycle.positivePart_apply, Affine.DivisorNorm.rationalPrincipalDivisor_apply,
    he, Int.cast_zero, max_self]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.EmbeddedDivisorDimension
