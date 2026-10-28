import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ChowPointClass

/-! # Point Chow All Grades -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.PointChowAllGrades.BundleCycles

noncomputable section

/-! The complete principal divisor has zero Chow class in every
dimension grade; grading outside its support dimension contributes zero. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem schemePrincipalPointDivisor_off_dimension (d : ℕ) (W : IrreducibleCloseds X)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f ≠ d + 1)
    (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d) : Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g x.val = 0 := by
  by_contra hn
  exact hW ((Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor_dimension f W g x.val hn).symm.trans
    (congrArg (fun n : ℕ => n + 1) x.property))

theorem schemeDimensionComponent_principal_off (d : ℕ) (W : IrreducibleCloseds X)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f ≠ d + 1) :
    Finite.ChowPointClass.BundleCycles.schemeDimensionComponent f d (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g) = 0 := by
  apply Finsupp.ext
  intro x
  exact schemePrincipalPointDivisor_off_dimension f d W g hW x

theorem pointCycleToChowQ_principal_all_grades (d : ℕ) (W : IrreducibleCloseds X)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) : Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g) = 0 := by
  by_cases hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1
  · exact Point.CycleChow.BundleCycles.pointCycleToChowQ_principal f d W hW g
  · exact (congrArg (DimensionChow.BundleCycles.dimensionCycleToChowQ f d) (schemeDimensionComponent_principal_off f d W g hW)).trans
      (map_zero (DimensionChow.BundleCycles.dimensionCycleToChowQ f d))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.PointChowAllGrades.BundleCycles
