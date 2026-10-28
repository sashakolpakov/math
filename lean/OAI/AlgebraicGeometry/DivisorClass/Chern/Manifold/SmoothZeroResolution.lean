import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.ManifoldIntegration
import OAI.AlgebraicGeometry.DivisorClass.Chern.AugmentedCochainZeroIso

/-! # Smooth Zero Resolution -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.SmoothZeroResolution

noncomputable section

/-! The genuine smooth singular sheaf complex resolves the original locally constant coefficients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem manifoldSmoothSheafAugmentation_d :
    AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.locallyConstantManifoldSmoothSheafAugmentation E M ≫
      (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex E M (ModuleCat.of ℂ ℂ)).d 0 1 = 0 := by
  rw [AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.locallyConstantManifoldSmoothSheafAugmentation_eq_singular_comp, Category.assoc,
    (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafRestriction E M (ModuleCat.of ℂ ℂ)).comm,
    ← Category.assoc]
  erw [AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation_d]
  exact zero_comp

theorem manifoldSmoothSheafAugmentation_exact_mono :
    (AugmentedResolutionComparison.augmentedZeroSequence (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex E M (ModuleCat.of ℂ ℂ))
      (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.locallyConstantManifoldSmoothSheafAugmentation E M) (manifoldSmoothSheafAugmentation_d E M)).Exact ∧
      Mono (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.locallyConstantManifoldSmoothSheafAugmentation E M) := by
  have := AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.quasiIso_manifoldSmoothSheafResolutionMap E M
  have hq : QuasiIsoAt (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafResolutionMap E M) 0 := inferInstance
  rw [CochainComplex.quasiIsoAt₀_iff] at hq
  have h := (ShortComplex.quasiIso_iff_of_zeros _ (by rfl) (by rfl)
    (by
      change (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex E M (ModuleCat.of ℂ ℂ)).d 0 0 = 0
      exact (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex E M (ModuleCat.of ℂ ℂ)).shape 0 0 (by simp))).mp hq
  change (ShortComplex.mk ((AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafResolutionMap E M).f 0)
    ((AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex E M (ModuleCat.of ℂ ℂ)).d 0 1) _).Exact ∧
    Mono ((AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafResolutionMap E M).f 0) at h
  simpa only [AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafResolutionMap_f_zero, AugmentedResolutionComparison.augmentedZeroSequence] using h

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem abelianManifoldSmoothAugmentation_d :
    Abelian.ManifoldIntegration.abelianManifoldSmoothAugmentation E M ≫ (Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M).d 0 1 = 0 := by
  change (Complex.SheafForget.complexSheafForget (TopCat.of M)).map _ ≫ (Complex.SheafForget.complexSheafForget (TopCat.of M)).map _ = 0
  rw [← Functor.map_comp, manifoldSmoothSheafAugmentation_d, Functor.map_zero]

def abelianManifoldSmoothZeroSequence :=
  AugmentedResolutionComparison.augmentedZeroSequence (Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M) (Abelian.ManifoldIntegration.abelianManifoldSmoothAugmentation E M)
    (abelianManifoldSmoothAugmentation_d E M)

theorem abelianManifoldSmoothZeroSequence_exact : (abelianManifoldSmoothZeroSequence E M).Exact :=
  (manifoldSmoothSheafAugmentation_exact_mono E M).1.map (Complex.SheafForget.complexSheafForget (TopCat.of M))

instance abelianManifoldSmoothAugmentation_mono : Mono (Abelian.ManifoldIntegration.abelianManifoldSmoothAugmentation E M) := by
  have := (manifoldSmoothSheafAugmentation_exact_mono E M).2
  exact inferInstanceAs (Mono ((Complex.SheafForget.complexSheafForget (TopCat.of M)).map
    (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.locallyConstantManifoldSmoothSheafAugmentation E M)))

theorem abelianManifoldSmoothComplex_exact (n : ℕ) :
    (Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M).ExactAt (n + 1) := by
  apply (Complex.SheafForget.complexSheafForgetComplex_exactAt_iff _ _).mpr
  have := AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.quasiIso_manifoldSmoothSheafResolutionMap E M
  apply (exactAt_iff_of_quasiIsoAt (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafResolutionMap E M) (n + 1)).mp
  exact HomologicalComplex.exactAt_single_obj (.up ℕ) 0 _ (n + 1) (Nat.succ_ne_zero n)

def abelianManifoldSmoothZeroIso :
    Abelian.ManifoldDeRham.abelianLocallyConstantComplexSheaf (TopCat.of M) ≅ (Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M).homology 0 :=
  AugmentedCochainZeroIso.augmentedCochainZeroIso _ _ (abelianManifoldSmoothAugmentation_d E M)
    (abelianManifoldSmoothZeroSequence_exact E M)

theorem abelianManifoldSmoothZeroIso_augmentation :
    (abelianManifoldSmoothZeroIso E M).hom ≫
      (HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation (Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M)).f 0 =
        Abelian.ManifoldIntegration.abelianManifoldSmoothAugmentation E M :=
  AugmentedCochainZeroIso.augmentedCochainZeroIso_augmentation _ _ _ _

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.SmoothZeroResolution
