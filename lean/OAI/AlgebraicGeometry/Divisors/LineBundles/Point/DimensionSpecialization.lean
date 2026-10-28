import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.PushforwardDimensionDrop

/-! # Dimension Specialization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Point.DimensionSpecialization.BundleCycles

/-! The actual dimension of a point closure decreases under specialization. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem pointClosure_dimension_specializes {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] {x y : X} (h : x ⤳ y) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y) f ≤
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f := by
  have hy : y ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)) := by
    rw [CycleClass.Geometric.GenericPoint.range_reducedSupportι]
    exact specializes_iff_mem_closure.mp h
  obtain ⟨z, rfl⟩ := hy
  rw [SupportDimension.BundleCycles.pointClosure_dimension_closedImmersion]
  exact Principal.PushforwardDimensionDrop.BundleCycles.pointDimension_le_schemeDimension (CycleClass.Geometric.SupportFiniteType.supportStructureMap (irreducibleSetEquivPoints.symm x) f) z

end OAI.AlgebraicGeometry.Divisors.LineBundles.Point.DimensionSpecialization.BundleCycles
