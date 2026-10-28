import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecializationComparison
import OAI.AlgebraicGeometry.Divisors.LineBundles.PointClassOffGrade
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CycleDimensionDecomposition
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.ChowTransport

/-! # Chow Point Specialization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.ChowPointSpecialization.BundleCycles

noncomputable section

/-! Chow specialization agrees with the full finite point-cycle
specialization formula in every dimension grade. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (I : X.IdealSheafData) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem globalChowSpecialization_pointClass_dimension (e d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f e →₀ ℚ) :
    ChowSpecialization.BundleCycles.globalChowSpecialization I f d (Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f e z)) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ (SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) d
        (CycleSpecialization.BundleCycles.globalCycleSpecialization I (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f e z)) := by
  have hf := LinearMap.congr_fun (Graded.GlobalSpecialization.BundleCycles.globalGradedCycleSpecialization_push I f e) z
  change Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) e
      (Graded.GlobalSpecialization.BundleCycles.globalGradedCycleSpecialization I f e z) =
    CycleSpecialization.BundleCycles.globalCycleSpecialization I (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f e z) at hf
  rw [← hf]
  by_cases hde : d = e
  · subst d
    rw [Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion, Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion, SpecializationComparison.BundleCycles.globalChowSpecialization_grading]
  · rw [PointClassOffGrade.BundleCycles.pointCycleToChowQ_inclusion_off f e d (Ne.symm hde), map_zero,
      PointClassOffGrade.BundleCycles.pointCycleToChowQ_inclusion_off (SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) e d (Ne.symm hde)]

theorem globalChowSpecialization_pointClass (d : ℕ) (z : X →₀ ℚ) :
    ChowSpecialization.BundleCycles.globalChowSpecialization I f d (Point.CycleChow.BundleCycles.pointCycleToChowQ f d z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ (SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) d (CycleSpecialization.BundleCycles.globalCycleSpecialization I z) := by
  classical
  have hz := Point.CycleDimensionDecomposition.BundleCycles.pointCycle_dimension_decomposition f z
  conv_lhs => rw [← hz]
  conv_rhs => rw [← hz]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro e _
  exact globalChowSpecialization_pointClass_dimension I f e.val d _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.ChowPointSpecialization.BundleCycles
