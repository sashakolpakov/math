import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ComplexAugmentation
import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.SmoothZeroResolution
import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.AugmentationNaturality

/-! # Smooth Sheaf Comparison -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SmoothSheafComparison

noncomputable section

/-! Original rational coefficients and actual smooth singular sheaves under the native comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

def complexAbelianSmoothRestriction :
    ComplexSheafMap.complexAbelianSingularResolution (TopCat.of M) ⟶ Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M :=
  Complex.SheafForget.complexSheafForgetComplexMap (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafRestriction E M (ModuleCat.of ℂ ℂ))

theorem complexAbelianSmoothRestriction_augmentation :
    ComplexAugmentation.complexAbelianConstantAugmentation (TopCat.of M) ≫ (complexAbelianSmoothRestriction E M).f 0 =
      Abelian.ManifoldIntegration.abelianManifoldSmoothAugmentation E M := by
  change (Complex.SheafForget.complexSheafForget (TopCat.of M)).map (AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation (TopCat.of M)) ≫
    (Complex.SheafForget.complexSheafForget (TopCat.of M)).map ((AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafRestriction E M (ModuleCat.of ℂ ℂ)).f 0) = _
  rw [← Functor.map_comp, ← AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.locallyConstantManifoldSmoothSheafAugmentation_eq_singular_comp]
  rfl

def rationalManifoldSmoothSheafMap :
    BettiSheafComparison.rationalAbelianSingularResolution (TopCat.of M) ⟶ Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M :=
  ComplexSheafMap.rationalComplexSingularSheafMap (TopCat.of M) ≫ complexAbelianSmoothRestriction E M

theorem rationalManifoldSmoothSheafMap_augmentation :
    Abelian.SingularAugmentation.rationalAbelianConstantAugmentation (TopCat.of M) ≫ (rationalManifoldSmoothSheafMap E M).f 0 =
      ComplexPeriod.rationalConstantComplexSheafMap (TopCat.of M) ≫ Abelian.ManifoldIntegration.abelianManifoldSmoothAugmentation E M := by
  change Abelian.SingularAugmentation.rationalAbelianConstantAugmentation (TopCat.of M) ≫
    ((ComplexSheafMap.rationalComplexSingularSheafMap (TopCat.of M)).f 0 ≫ (complexAbelianSmoothRestriction E M).f 0) = _
  rw [← Category.assoc, ComplexAugmentation.rationalComplexSingularSheafMap_augmentation, Category.assoc,
    complexAbelianSmoothRestriction_augmentation]

open scoped _root_.Manifold ContDiff

variable [IsManifold 𝓘(ℝ, E) ∞ M] [LocallyPathConnectedSpace M]

theorem rationalManifoldSmoothSheafMap_zeroIso :
    (BettiSheafComparison.rationalConstantAbelianZeroIso (TopCat.of M)).hom ≫
        HomologicalComplex.homologyMap (rationalManifoldSmoothSheafMap E M) 0 =
      ComplexPeriod.rationalConstantComplexSheafMap (TopCat.of M) ≫ (Manifold.SmoothZeroResolution.abelianManifoldSmoothZeroIso E M).hom :=
  Intrinsic.AugmentationNaturality.cochainAugmentationZeroIso_naturality _ _ _ _ _ _
    (Abelian.SingularAugmentation.rationalAbelianConstantAugmentation_zeroIso (TopCat.of M))
    (Manifold.SmoothZeroResolution.abelianManifoldSmoothZeroIso_augmentation E M) (rationalManifoldSmoothSheafMap_augmentation E M)

variable [StronglyLocallyContractibleSpace M]

theorem rationalManifoldSmoothSheafMap_native (n : ℕ) :
    HomologicalComplex.homologyMap
        (((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSections (TopCat.of M)).mapHomologicalComplex (.up ℕ)).map
          (rationalManifoldSmoothSheafMap E M)) (n + 1) ≫
      Intrinsic.AugmentationNaturality.nativeSectionCohomologyMapOfZero (Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M)
        (Manifold.SmoothZeroResolution.abelianManifoldSmoothComplex_exact E M) (Manifold.SmoothZeroResolution.abelianManifoldSmoothZeroIso E M) n =
    Intrinsic.AugmentationNaturality.nativeSectionCohomologyMapOfZero (BettiSheafComparison.rationalAbelianSingularResolution (TopCat.of M))
        (BettiSheafComparison.rationalAbelianSingularResolution_exact (TopCat.of M)) (BettiSheafComparison.rationalConstantAbelianZeroIso (TopCat.of M)) n ≫
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology (TopCat.of M)) (n + 1)).map
        (ComplexPeriod.rationalConstantComplexSheafMap (TopCat.of M)) :=
  Intrinsic.AugmentationNaturality.nativeSectionCohomologyMapOfZero_naturality _ _ _ _ _ _ (rationalManifoldSmoothSheafMap_zeroIso E M) n

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SmoothSheafComparison
