import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Inclusion
import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SemilinearMap
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapCongr

/-! # Naturality -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Naturality.BundleCycles

noncomputable section

/-! The infinity hyperplane is compatible with actual changes of
coefficients and conormal generators. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R S M N : Type} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (f : R →+* S) (g : M →ₛₗ[f] N)

theorem symmetricInfinityGraded_naturality :
    (Symmetric.GradedMap.BundleCycles.symmetricGradedMap (LinearMap.snd S S N)).comp
      (Symmetric.ScalarGrading.BundleCycles.symmetricScalarGradedMap f (Augmented.SemilinearMap.BundleCycles.augmentedSemilinearMap f g)) =
    (Symmetric.ScalarGrading.BundleCycles.symmetricScalarGradedMap f g).comp (Symmetric.GradedMap.BundleCycles.symmetricGradedMap (LinearMap.snd R R M)) := by
  apply GradedRingHom.coe_ringHom_injective
  apply Symmetric.ScalarMap.BundleCycles.symmetricRingHom_ext
  · intro r
    change Symmetric.GradedMap.BundleCycles.symmetricGradedMap (LinearMap.snd S S N)
      (Symmetric.ScalarMap.BundleCycles.symmetricScalarMap f (Augmented.SemilinearMap.BundleCycles.augmentedSemilinearMap f g) (algebraMap R _ r)) =
      Symmetric.ScalarMap.BundleCycles.symmetricScalarMap f g (Symmetric.GradedMap.BundleCycles.symmetricGradedMap (LinearMap.snd R R M) (algebraMap R _ r))
    have hR : Symmetric.GradedMap.BundleCycles.symmetricGradedMap (LinearMap.snd R R M) (algebraMap R _ r) = algebraMap R _ r :=
      (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R M).comp (LinearMap.snd R R M))).commutes r
    have hS : Symmetric.GradedMap.BundleCycles.symmetricGradedMap (LinearMap.snd S S N) (algebraMap S _ (f r)) = algebraMap S _ (f r) :=
      (SymmetricAlgebra.lift ((SymmetricAlgebra.ι S N).comp (LinearMap.snd S S N))).commutes (f r)
    rw [Symmetric.ScalarMap.BundleCycles.symmetricScalarMap_algebraMap, hS, hR, Symmetric.ScalarMap.BundleCycles.symmetricScalarMap_algebraMap]
  · intro m
    change Symmetric.GradedMap.BundleCycles.symmetricGradedMap (LinearMap.snd S S N)
      (Symmetric.ScalarMap.BundleCycles.symmetricScalarMap f (Augmented.SemilinearMap.BundleCycles.augmentedSemilinearMap f g) (SymmetricAlgebra.ι R (R × M) m)) =
      Symmetric.ScalarMap.BundleCycles.symmetricScalarMap f g (Symmetric.GradedMap.BundleCycles.symmetricGradedMap (LinearMap.snd R R M) (SymmetricAlgebra.ι R (R × M) m))
    rw [Symmetric.ScalarMap.BundleCycles.symmetricScalarMap_generator, Symmetric.GradedMap.BundleCycles.symmetricGradedMap_generator, Symmetric.GradedMap.BundleCycles.symmetricGradedMap_generator,
      Symmetric.ScalarMap.BundleCycles.symmetricScalarMap_generator]
    rfl

theorem symmetricInfinityInclusion_naturality (hgen : Submodule.span S (Set.range g) = ⊤) :
    Inclusion.BundleCycles.symmetricInfinityInclusion S N ≫
      Symmetric.ScalarGrading.BundleCycles.symmetricScalarProjectiveMap f (Augmented.SemilinearMap.BundleCycles.augmentedSemilinearMap f g) (Augmented.SemilinearMap.BundleCycles.augmentedSemilinearMap_span f g hgen) =
    Symmetric.ScalarGrading.BundleCycles.symmetricScalarProjectiveMap f g hgen ≫ Inclusion.BundleCycles.symmetricInfinityInclusion R M := by
  change Proj.map _ _ ≫ Proj.map _ _ = Proj.map _ _ ≫ Proj.map _ _
  rw [← Proj.map_comp, ← Proj.map_comp]
  exact Projective.MapCongr.BundleCycles.projectiveMap_congr (symmetricInfinityGraded_naturality f g) _ _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Naturality.BundleCycles
