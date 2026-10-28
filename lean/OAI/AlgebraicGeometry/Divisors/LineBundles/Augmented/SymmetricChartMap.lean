import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricNaturality
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ChartMap

/-! # Symmetric Chart Map -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartMap.BundleCycles

noncomputable section

/-! The actual distinguished chart maps commute with dehomogenization. -/

open _root_.HomogeneousLocalization

variable {R S M N : Type} [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N] (f : R →+* S) (g : M →ₛₗ[f] N)

def augmentedSymmetricChartMap : SymmetricChart.BundleCycles.augmentedSymmetricChart R M →+* SymmetricChart.BundleCycles.augmentedSymmetricChart S N :=
  Graded.ChartMap.BundleCycles.gradedChartMap (Symmetric.ScalarGrading.BundleCycles.symmetricScalarGradedMap f (SemilinearMap.BundleCycles.augmentedSemilinearMap f g))
    (SymmetricChart.BundleCycles.augmentedSymmetricVariable R M) (SymmetricChart.BundleCycles.augmentedSymmetricVariable S N)
    (SymmetricNaturality.BundleCycles.augmentedSymmetricMap_variable f g)

theorem augmentedSymmetricChartMap_mk (n : ℕ) (a : SymmetricAlgebra R (R × M))
    (ha : a ∈ Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) (n • 1)) :
    augmentedSymmetricChartMap f g
      (Away.mk (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M)) (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) n a ha) =
    Away.mk (Symmetric.Grading.BundleCycles.symmetricGrading S (S × N)) (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree S N) n
      (Symmetric.ScalarMap.BundleCycles.symmetricScalarMap f (SemilinearMap.BundleCycles.augmentedSemilinearMap f g) a)
      ((Symmetric.ScalarGrading.BundleCycles.symmetricScalarGradedMap f (SemilinearMap.BundleCycles.augmentedSemilinearMap f g)).map_mem ha) :=
  Graded.ChartMap.BundleCycles.gradedChartMap_mk _ _ _ _ (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree S N) n a ha

theorem augmentedSymmetricDehomogenization_naturality :
    (SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization S N).comp (augmentedSymmetricChartMap f g) =
      (Symmetric.ScalarMap.BundleCycles.symmetricScalarMap f g).comp (SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization R M) := by
  apply RingHom.ext
  intro z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M))
    (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) z
  change SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization S N
    (augmentedSymmetricChartMap f g (Away.mk (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M))
      (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) n a ha)) = _
  rw [augmentedSymmetricChartMap_mk]
  exact (SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization_mk S N n
    (Symmetric.ScalarMap.BundleCycles.symmetricScalarMap f (SemilinearMap.BundleCycles.augmentedSemilinearMap f g) a)
    (Symmetric.ScalarGrading.BundleCycles.symmetricScalarMap_mem_grade f (SemilinearMap.BundleCycles.augmentedSemilinearMap f g) (n • 1) a ha)).trans
      ((DFunLike.congr_fun (SymmetricNaturality.BundleCycles.symmetricDehomogenizingMap_naturality f g) a).trans
        (congrArg (Symmetric.ScalarMap.BundleCycles.symmetricScalarMap f g) (SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization_mk R M n a ha).symm))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartMap.BundleCycles
