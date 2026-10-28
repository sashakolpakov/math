import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.Intersection
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SupportComparison

/-! # Intersection Comparison -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.IntersectionComparison.Cycles

noncomputable section

/-! # LineBundleCycles: cycle intersection is invariant under actual line-bundle isomorphisms in Chow -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] {L M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X}
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ)

theorem lineBundleGradedDivisor_class (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (W : IrreducibleCloseds X) :
    DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Intersection.Cycles.lineBundleGradedDivisor L f d W) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Intersection.Cycles.lineBundleDivisorOnSupport L W) := rfl

theorem lineBundleCycleIntersection_class_iso (e : L.sheaf ≅ M.sheaf)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + 1) →₀ ℚ) :
    DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Intersection.Cycles.lineBundleCycleIntersection L f d z) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Intersection.Cycles.lineBundleCycleIntersection M f d z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw]
  | single x a =>
    rw [Intersection.Cycles.lineBundleCycleIntersection_single, Intersection.Cycles.lineBundleCycleIntersection_single, map_smul, map_smul,
      lineBundleGradedDivisor_class, lineBundleGradedDivisor_class,
      SupportComparison.Cycles.lineBundleDivisorOnSupport_class_iso e f d _ x.property]

theorem lineBundleCycleIntersection_class_global (e : L.sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule X)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + 1) →₀ ℚ) :
    DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Intersection.Cycles.lineBundleCycleIntersection L f d z) = 0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw, add_zero]
  | single x a =>
    rw [Intersection.Cycles.lineBundleCycleIntersection_single, map_smul, lineBundleGradedDivisor_class,
      SupportComparison.Cycles.lineBundleDivisorOnSupport_class_global e f d _ x.property, smul_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.IntersectionComparison.Cycles
