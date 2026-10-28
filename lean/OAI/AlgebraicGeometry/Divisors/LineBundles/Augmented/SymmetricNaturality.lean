import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SemilinearMap
import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChart

/-! # Symmetric Naturality -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricNaturality.BundleCycles

noncomputable section

/-! Dehomogenization of the augmented symmetric algebra commutes with
actual semilinear coefficient changes. -/

variable {R S M N : Type} [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N] (f : R →+* S) (g : M →ₛₗ[f] N)

theorem augmentedSymmetricMap_variable :
    Symmetric.ScalarMap.BundleCycles.symmetricScalarMap f (SemilinearMap.BundleCycles.augmentedSemilinearMap f g) (SymmetricChart.BundleCycles.augmentedSymmetricVariable R M) =
      SymmetricChart.BundleCycles.augmentedSymmetricVariable S N := by
  unfold SymmetricChart.BundleCycles.augmentedSymmetricVariable
  rw [Symmetric.ScalarMap.BundleCycles.symmetricScalarMap_generator, SemilinearMap.BundleCycles.augmentedSemilinearMap_variable]

theorem symmetricDehomogenizingMap_naturality :
    (SymmetricChart.BundleCycles.symmetricDehomogenizingMap S N).toRingHom.comp
      (Symmetric.ScalarMap.BundleCycles.symmetricScalarMap f (SemilinearMap.BundleCycles.augmentedSemilinearMap f g)) =
    (Symmetric.ScalarMap.BundleCycles.symmetricScalarMap f g).comp (SymmetricChart.BundleCycles.symmetricDehomogenizingMap R M).toRingHom := by
  apply Symmetric.ScalarMap.BundleCycles.symmetricRingHom_ext
  · intro r
    change SymmetricChart.BundleCycles.symmetricDehomogenizingMap S N
      (Symmetric.ScalarMap.BundleCycles.symmetricScalarMap f (SemilinearMap.BundleCycles.augmentedSemilinearMap f g) (algebraMap R _ r)) =
      Symmetric.ScalarMap.BundleCycles.symmetricScalarMap f g (SymmetricChart.BundleCycles.symmetricDehomogenizingMap R M (algebraMap R _ r))
    rw [Symmetric.ScalarMap.BundleCycles.symmetricScalarMap_algebraMap, AlgHom.commutes, AlgHom.commutes,
      Symmetric.ScalarMap.BundleCycles.symmetricScalarMap_algebraMap]
  · rintro ⟨r, m⟩
    change SymmetricChart.BundleCycles.symmetricDehomogenizingMap S N
      (Symmetric.ScalarMap.BundleCycles.symmetricScalarMap f (SemilinearMap.BundleCycles.augmentedSemilinearMap f g) (SymmetricAlgebra.ι R (R × M) (r, m))) =
      Symmetric.ScalarMap.BundleCycles.symmetricScalarMap f g (SymmetricChart.BundleCycles.symmetricDehomogenizingMap R M (SymmetricAlgebra.ι R (R × M) (r, m)))
    rw [Symmetric.ScalarMap.BundleCycles.symmetricScalarMap_generator, SymmetricChart.BundleCycles.symmetricDehomogenizingMap_generator R M r m, map_add,
      Symmetric.ScalarMap.BundleCycles.symmetricScalarMap_algebraMap, Symmetric.ScalarMap.BundleCycles.symmetricScalarMap_generator]
    exact SymmetricChart.BundleCycles.symmetricDehomogenizingMap_generator S N (f r) (g m)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricNaturality.BundleCycles
