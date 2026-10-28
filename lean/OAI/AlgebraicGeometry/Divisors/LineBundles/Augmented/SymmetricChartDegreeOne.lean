import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartGenerators
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ChartMultiplication

/-! # Symmetric Chart Degree One -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartDegreeOne.BundleCycles

noncomputable section

/-! Normalizing an arbitrary degree-one generator at the distinguished
coordinate gives its dehomogenization in the actual chart. -/

open _root_.HomogeneousLocalization

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

attribute [local instance] SymmetricChartGenerators.BundleCycles.augmentedSymmetricChartAlgebra

theorem augmentedSymmetricGenerator_split (r : R) (m : M) :
    SymmetricAlgebra.ι R (R × M) (r, m) =
      r • SymmetricChart.BundleCycles.augmentedSymmetricVariable R M + SymmetricChartGenerators.BundleCycles.augmentedSymmetricModuleLinear R M m := by
  change SymmetricAlgebra.ι R (R × M) (r, m) =
    r • SymmetricAlgebra.ι R (R × M) (1, 0) + SymmetricAlgebra.ι R (R × M) (0, m)
  rw [← map_smul, ← map_add]
  congr 1
  ext <;> simp

theorem augmentedSymmetricChart_degreeOne (v : R × M)
    (hv : SymmetricAlgebra.ι R (R × M) v ∈ Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) (1 • 1)) :
    SymmetricChartGenerators.BundleCycles.augmentedSymmetricChartInverse R M
      (SymmetricChart.BundleCycles.symmetricDehomogenizingMap R M (SymmetricAlgebra.ι R (R × M) v)) =
        Away.mk (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M)) (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) 1
          (SymmetricAlgebra.ι R (R × M) v) hv := by
  obtain ⟨r, m⟩ := v
  rw [SymmetricChart.BundleCycles.symmetricDehomogenizingMap_generator, map_add, AlgHom.commutes,
    SymmetricChartGenerators.BundleCycles.augmentedSymmetricChartInverse_generator]
  have ht : SymmetricChart.BundleCycles.augmentedSymmetricVariable R M ∈ Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) (1 • 1) := by
    simpa only [one_smul] using SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M
  have hm : SymmetricChartGenerators.BundleCycles.augmentedSymmetricModuleLinear R M m ∈ Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) (1 • 1) := by
    simpa only [one_smul] using SymmetricChartGenerators.BundleCycles.augmentedSymmetricModuleLinear_degree R M m
  have hsplit : (⟨SymmetricAlgebra.ι R (R × M) (r, m), hv⟩ : Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) (1 • 1)) =
      r • ⟨SymmetricChart.BundleCycles.augmentedSymmetricVariable R M, ht⟩ + ⟨SymmetricChartGenerators.BundleCycles.augmentedSymmetricModuleLinear R M m, hm⟩ :=
    Subtype.ext (augmentedSymmetricGenerator_split R M r m)
  have h := congrArg
    (Graded.ChartAddition.BundleCycles.gradedChartFractionLinear (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M)) (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) 1)
    hsplit
  refine (h.trans ((Graded.ChartAddition.BundleCycles.gradedAway_mk_add (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M))
    (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) 1 (r • SymmetricChart.BundleCycles.augmentedSymmetricVariable R M)
      (SymmetricChartGenerators.BundleCycles.augmentedSymmetricModuleLinear R M m) ((Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) (1 • 1)).smul_mem r ht) hm).trans ?_)).symm
  rw [Graded.ChartAddition.BundleCycles.gradedChartFraction_smul (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M))
    (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) 1 r (SymmetricChart.BundleCycles.augmentedSymmetricVariable R M) ht,
    Graded.ChartMultiplication.BundleCycles.gradedAway_mk_self, mul_one]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartDegreeOne.BundleCycles
