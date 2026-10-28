import OAI.AlgebraicGeometry.Comparison.Betti.IntegrationDerivedNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.AugmentationCoefficientNormalization

/-! # Constant Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.ConstantNormalization.Integration

noncomputable section

/-! The original standard-constant de Rham augmentation is the locally
constant augmentation composed with the actual coefficient identification. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.Comparison.Betti.AugmentationCoefficientNormalization.ComplexExtension

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

local instance smoothConstantHasDerived : HasDerivedCategory.{1} (ConstantSheafSections.ComplexSheaves (TopCat.of M)) :=
  HasDerivedCategory.standard _

abbrev smoothConstantCoefficientIso : ConstantSheafSections.standardConstantSheaf (TopCat.of M) ≅
    InjectiveExtPullback.locallyConstantCoefficients (TopCat.of M) := Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn (TopCat.of M)

abbrev smoothStandardAugmentation :
    (CochainComplex.single₀ (ConstantSheafSections.ComplexSheaves (TopCat.of M))).obj
        (ConstantSheafSections.standardConstantSheaf (TopCat.of M)) ⟶ Filtered.DerivedInclusion.Hodge.smoothSheafComplexNat E M :=
  Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldDeRhamSheafAugmentation E M

omit [FiniteDimensional ℝ E] in
theorem smoothStandardAugmentation_factorization :
    smoothStandardAugmentation E M =
      (CochainComplex.single₀ (ConstantSheafSections.ComplexSheaves (TopCat.of M))).map
        (smoothConstantCoefficientIso M).hom ≫ IntegrationDerivedNormalization.smoothLocallyConstantAugmentation E M := by
  exact AugmentationCoefficientNormalization.ComplexExtension.fromSingleAugmentation_precomp (C := ConstantSheafSections.ComplexSheaves (TopCat.of M))
    (K := Filtered.DerivedInclusion.Hodge.smoothSheafComplexNat E M) (smoothConstantCoefficientIso M).hom
    (Analysis.DifferentialForms.Manifold.LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf E M) (Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldLocallyConstantToDeRham_comp_d E M)

def smoothStandardResolutionIso :
    (DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves (TopCat.of M)) 0).obj
        (ConstantSheafSections.standardConstantSheaf (TopCat.of M)) ≅
      DerivedCategory.Q.obj ((Filtered.DerivedInclusion.Hodge.smoothSheafComplexNat E M).extend (ComplexShape.embeddingUpIntGE 0)) :=
  (DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves (TopCat.of M)) 0).mapIso
    (smoothConstantCoefficientIso M) ≪≫ IntegrationDerivedNormalization.smoothLocallyConstantResolutionIso E M

theorem smoothStandardResolutionIso_hom :
    (smoothStandardResolutionIso E M).hom =
      DerivedCategory.Q.map (AugmentationExtension.Complex.extendAugmentation (smoothStandardAugmentation E M)) := by
  rw [smoothStandardAugmentation_factorization]
  erw [AugmentationCoefficientNormalization.ComplexExtension.extendAugmentation_precomp]
  erw [CategoryTheory.Functor.map_comp]
  rfl

theorem smoothStandardResolutionIso_inverse :
    (IntegrationDerivedNormalization.smoothLocallyConstantResolutionIso E M).inv ≫
      (DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves (TopCat.of M)) 0).map
        (smoothConstantCoefficientIso M).inv =
      (smoothStandardResolutionIso E M).inv := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.ConstantNormalization.Integration
