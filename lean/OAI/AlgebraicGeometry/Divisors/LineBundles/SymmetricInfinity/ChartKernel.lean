import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Inclusion
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.PrincipalChartKernel
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.HyperplaneCharts

/-! # Chart Kernel -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.ChartKernel.BundleCycles

noncomputable section

/-! The closed infinity hyperplane has the actual regular principal
ideal in each degree-one affine chart. -/

open _root_.HomogeneousLocalization

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

theorem symmetricInfinity_chart_kernel (v : R × M) :
    RingHom.ker (Away.map (Symmetric.GradedMap.BundleCycles.symmetricGradedMap (LinearMap.snd R R M)) (SymmetricAlgebra.ι R (R × M) v)) =
      Ideal.span {Symmetric.HyperplaneCharts.BundleCycles.symmetricHyperplaneCoordinate R M v} := by
  have h := Graded.PrincipalChartKernel.BundleCycles.gradedPrincipalChart_kernel (Symmetric.GradedMap.BundleCycles.symmetricGradedMap (LinearMap.snd R R M))
    (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) (Symmetric.DegreeOneCover.BundleCycles.symmetricGenerator_degree R (R × M) v)
    (Kernel.BundleCycles.symmetricInfinity_kernel R M)
  have he : Symmetric.HyperplaneCharts.BundleCycles.symmetricHyperplaneCoordinate R M v =
      Away.mk (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M)) (Symmetric.DegreeOneCover.BundleCycles.symmetricGenerator_degree R (R × M) v) 1
        (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable R M) (by simpa only [one_smul] using Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) := by
    unfold Symmetric.HyperplaneCharts.BundleCycles.symmetricHyperplaneCoordinate
    apply HomogeneousLocalization.val_injective
    rw [Away.val_mk, Away.val_mk, pow_one]
  exact h.trans (congrArg (fun x => Ideal.span {x}) he.symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.ChartKernel.BundleCycles
