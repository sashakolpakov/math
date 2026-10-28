import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.AffineCompactification
import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartMap
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ChartMap

/-! # Compactification Naturality -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.CompactificationNaturality.BundleCycles

noncomputable section

/-! The actual affine compactification commutes with semilinear maps
whose image generates the target module. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R S M N : Type} [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N] (f : R →+* S) (g : M →ₛₗ[f] N)
    (hgen : Submodule.span S (Set.range g) = ⊤)

theorem symmetricAffineCompactification_naturality :
    Spec.map (CommRingCat.ofHom (ScalarMap.BundleCycles.symmetricScalarMap f g)) ≫ AffineCompactification.BundleCycles.symmetricAffineCompactification R M =
      AffineCompactification.BundleCycles.symmetricAffineCompactification S N ≫
        ScalarGrading.BundleCycles.symmetricScalarProjectiveMap f (Augmented.SemilinearMap.BundleCycles.augmentedSemilinearMap f g) (Augmented.SemilinearMap.BundleCycles.augmentedSemilinearMap_span f g hgen) := by
  unfold AffineCompactification.BundleCycles.symmetricAffineCompactification ScalarGrading.BundleCycles.symmetricScalarProjectiveMap
  rw [← Category.assoc, ← Spec.map_comp]
  have hn : CommRingCat.ofHom (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization R M) ≫
      CommRingCat.ofHom (ScalarMap.BundleCycles.symmetricScalarMap f g) =
    CommRingCat.ofHom (Augmented.SymmetricChartMap.BundleCycles.augmentedSymmetricChartMap f g) ≫
      CommRingCat.ofHom (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization S N) := by
    apply CommRingCat.hom_ext
    exact (Augmented.SymmetricChartMap.BundleCycles.augmentedSymmetricDehomogenization_naturality f g).symm
  rw [hn, Spec.map_comp, Category.assoc, Category.assoc]
  exact congrArg (fun k => Spec.map (CommRingCat.ofHom (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization S N)) ≫ k)
    (Projective.ChartMap.BundleCycles.gradedChartMap_awayι (ScalarGrading.BundleCycles.symmetricScalarGradedMap f (Augmented.SemilinearMap.BundleCycles.augmentedSemilinearMap f g))
    (ScalarGrading.BundleCycles.symmetricScalarGradedMap_irrelevant f (Augmented.SemilinearMap.BundleCycles.augmentedSemilinearMap f g)
      (Augmented.SemilinearMap.BundleCycles.augmentedSemilinearMap_span f g hgen))
    (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable R M) (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable S N)
    (Augmented.SymmetricNaturality.BundleCycles.augmentedSymmetricMap_variable f g) (by decide : 0 < 1)
    (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree S N))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.CompactificationNaturality.BundleCycles
