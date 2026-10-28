import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.ImmersionSupport
import OAI.AlgebraicGeometry.CycleClass.Geometric.StratumClosure

/-! # Point Closure Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.PointClosureDimension

noncomputable section

/-! Closed embeddings preserve the actual function-field dimension
of point closures. A closed section and its retraction therefore do too. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {Y Z : Scheme} (i : Y ⟶ Z) [IsClosedImmersion i]

omit [IsClosedImmersion i] in
theorem image (y : Y) :
    CycleClass.Geometric.StratumClosure.integralImageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm y) ≫ i) =
      irreducibleSetEquivPoints.symm (i y) := by
  apply irreducibleSetEquivPoints.injective
  change CycleClass.Thom.IntersectionGeometry.supportPoint (CycleClass.Geometric.StratumClosure.integralImageClosure
    (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm y) ≫ i)) =
      CycleClass.Thom.IntersectionGeometry.supportPoint (irreducibleSetEquivPoints.symm (i y))
  have h := ImmersionSupport.support_point
    (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm y) ≫ i)
  exact h.trans ((congrArg i ((CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq (irreducibleSetEquivPoints.symm y)).trans
    ((irreducibleSetEquivPoints (α := Y)).apply_symm_apply y))).trans
      ((irreducibleSetEquivPoints (α := Z)).apply_symm_apply (i y)).symm)

theorem dimension {k : Type} [Field k] (f : Z ⟶ Spec (.of k)) (y : Y) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y) (i ≫ f) =
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (i y)) f := by
  have hd := CycleClass.Geometric.StratumClosure.schemeTranscendenceDimension_eq_imageClosure
    (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm y) ≫ i) f
  rw [image] at hd
  simpa only [Foundations.Scheme.SupportDimension.supportTranscendenceDimension, CycleClass.Geometric.SupportFiniteType.supportStructureMap, Category.assoc] using hd

theorem retraction (q : Z ⟶ Y) (h : i ≫ q = 𝟙 Y)
    {k : Type} [Field k] (f : Y ⟶ Spec (.of k)) (y : Y) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (i y)) (q ≫ f) =
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y) f := by
  have hd := dimension i (q ≫ f) y
  rw [← Category.assoc, h, Category.id_comp] at hd
  exact hd.symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.PointClosureDimension
