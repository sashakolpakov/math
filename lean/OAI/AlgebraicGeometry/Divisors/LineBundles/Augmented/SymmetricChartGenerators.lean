import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ChartAddition

/-! # Symmetric Chart Generators -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartGenerators.BundleCycles

noncomputable section

/-! The inverse affine-chart map sends a module generator to its genuine
homogeneous fraction with denominator the distinguished coordinate. -/

open _root_.HomogeneousLocalization

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

abbrev augmentedSymmetricChartAlgebra : Algebra R (SymmetricChart.BundleCycles.augmentedSymmetricChart R M) :=
  Graded.ChartAddition.BundleCycles.gradedChartScalarAlgebra (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M)) (SymmetricChart.BundleCycles.augmentedSymmetricVariable R M)

attribute [local instance] augmentedSymmetricChartAlgebra

def augmentedSymmetricModuleLinear : M →ₗ[R] SymmetricAlgebra R (R × M) :=
  (SymmetricAlgebra.ι R (R × M)).comp (LinearMap.inr R R M)

theorem augmentedSymmetricModuleLinear_degree (m : M) :
    augmentedSymmetricModuleLinear R M m ∈ Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) 1 := by
  change SymmetricAlgebra.ι R (R × M) (0, m) ∈ LinearMap.range (SymmetricAlgebra.ι R (R × M)) ^ 1
  simpa only [pow_one] using LinearMap.mem_range_self (SymmetricAlgebra.ι R (R × M)) (0, m)

def augmentedSymmetricChartGenerator : M →ₗ[R] SymmetricChart.BundleCycles.augmentedSymmetricChart R M :=
  (Graded.ChartAddition.BundleCycles.gradedChartFractionLinear (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M)) (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) 1).comp
    ((augmentedSymmetricModuleLinear R M).codRestrict _ (fun m => by
      simpa only [one_smul] using augmentedSymmetricModuleLinear_degree R M m))

def augmentedSymmetricChartInverse : SymmetricAlgebra R M →ₐ[R] SymmetricChart.BundleCycles.augmentedSymmetricChart R M :=
  SymmetricAlgebra.lift (augmentedSymmetricChartGenerator R M)

theorem augmentedSymmetricChartInverse_generator (m : M) :
    augmentedSymmetricChartInverse R M (SymmetricAlgebra.ι R M m) =
      Away.mk (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M)) (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) 1
        (augmentedSymmetricModuleLinear R M m) (by simpa only [one_smul] using augmentedSymmetricModuleLinear_degree R M m) :=
  SymmetricAlgebra.lift_ι_apply _ m

theorem augmentedSymmetricDehomogenization_generator (m : M) :
    SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization R M (augmentedSymmetricChartGenerator R M m) =
      SymmetricAlgebra.ι R M m := by
  exact (SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization_mk R M 1
    (augmentedSymmetricModuleLinear R M m)
    (by simpa only [one_smul] using augmentedSymmetricModuleLinear_degree R M m)).trans (by
      change SymmetricChart.BundleCycles.symmetricDehomogenizingMap R M (SymmetricAlgebra.ι R (R × M) (0, m)) = _
      rw [SymmetricChart.BundleCycles.symmetricDehomogenizingMap_generator, map_zero, zero_add])

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartGenerators.BundleCycles
