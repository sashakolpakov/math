import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartGenerators

/-! # Symmetric Chart Scalar -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartScalar.BundleCycles

noncomputable section

/-! Dehomogenization respects the actual coefficient-ring structure on
the distinguished homogeneous chart. -/

open _root_.HomogeneousLocalization

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

attribute [local instance] SymmetricChartGenerators.BundleCycles.augmentedSymmetricChartAlgebra

theorem augmentedSymmetricDehomogenization_scalar (r : R) :
    SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization R M (algebraMap R (SymmetricChart.BundleCycles.augmentedSymmetricChart R M) r) =
      algebraMap R (SymmetricAlgebra R M) r := by
  have h := Graded.ChartAddition.BundleCycles.gradedAway_mk_algebraMap (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M))
    (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) (algebraMap R (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) 0) r)
  change SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization R M
    (fromZeroRingHom (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M)) (Submonoid.powers (SymmetricChart.BundleCycles.augmentedSymmetricVariable R M))
      (algebraMap R (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) 0) r)) = _
  rw [← h]
  exact (SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization_mk R M 0 _ _).trans
    ((SymmetricChart.BundleCycles.symmetricDehomogenizingMap R M).commutes r)

def augmentedSymmetricDehomogenizationAlg : SymmetricChart.BundleCycles.augmentedSymmetricChart R M →ₐ[R] SymmetricAlgebra R M :=
  { SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization R M with
    commutes' := augmentedSymmetricDehomogenization_scalar R M }

theorem augmentedSymmetricDehomogenization_leftInverse :
    Function.LeftInverse (SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization R M) (SymmetricChartGenerators.BundleCycles.augmentedSymmetricChartInverse R M) := by
  have h : (augmentedSymmetricDehomogenizationAlg R M).comp (SymmetricChartGenerators.BundleCycles.augmentedSymmetricChartInverse R M) =
      AlgHom.id R (SymmetricAlgebra R M) := by
    apply SymmetricAlgebra.algHom_ext
    ext m
    change SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization R M
      (SymmetricAlgebra.lift (SymmetricChartGenerators.BundleCycles.augmentedSymmetricChartGenerator R M) (SymmetricAlgebra.ι R M m)) = _
    rw [SymmetricAlgebra.lift_ι_apply]
    exact SymmetricChartGenerators.BundleCycles.augmentedSymmetricDehomogenization_generator R M m
  exact fun a => DFunLike.congr_fun h a

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartScalar.BundleCycles
