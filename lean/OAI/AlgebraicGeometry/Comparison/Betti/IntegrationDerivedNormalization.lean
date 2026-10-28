import OAI.AlgebraicGeometry.Comparison.Betti.IntegrationCocycleNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.NonnegativeResolutionClasses

/-! # Integration Derived Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.IntegrationDerivedNormalization

noncomputable section

/-! The actual integration cocycle represents precisely the smooth derived
class followed by the inverse of the original locally constant augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

local instance integrationDerivedHasDerived : HasDerivedCategory.{1} (ConstantSheafSections.ComplexSheaves (TopCat.of M)) := HasDerivedCategory.standard _
local instance integrationDerivedHasExt : HasExt.{1} (ConstantSheafSections.ComplexSheaves (TopCat.of M)) := hasExt_of_hasDerivedCategory _

abbrev smoothLocallyConstantAugmentation :
    (CochainComplex.single₀ (ConstantSheafSections.ComplexSheaves (TopCat.of M))).obj
        (InjectiveExtPullback.locallyConstantCoefficients (TopCat.of M)) ⟶ Filtered.DerivedInclusion.Hodge.smoothSheafComplexNat E M :=
  Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldLocallyConstantDeRhamAugmentation E M

instance smoothLocallyConstantAugmentation_quasiIso : QuasiIso (smoothLocallyConstantAugmentation E M) := by
  have h := Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldLocallyConstantDeRhamAugmentation_quasiIso E M
  exact h

def smoothLocallyConstantResolutionIso :
    (DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves (TopCat.of M)) 0).obj
        (InjectiveExtPullback.locallyConstantCoefficients (TopCat.of M)) ≅
      DerivedCategory.Q.obj ((Filtered.DerivedInclusion.Hodge.smoothSheafComplexNat E M).extend (ComplexShape.embeddingUpIntGE 0)) := by
  let Q : CochainComplex (ConstantSheafSections.ComplexSheaves (TopCat.of M)) ℤ ⥤
      DerivedCategory (ConstantSheafSections.ComplexSheaves (TopCat.of M)) := DerivedCategory.Q
  have h : IsIso (Q.map (AugmentationExtension.Complex.extendAugmentation (smoothLocallyConstantAugmentation E M))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  exact @asIso _ _ _ _ (Q.map (AugmentationExtension.Complex.extendAugmentation (smoothLocallyConstantAugmentation E M))) h

theorem smoothForm_injectiveExt_derivedClass (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (ha : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0) :
    (InjectiveExtPullback.injectiveHomologyExtEquiv (TopCat.of M) n
      (HomologicalComplex.homologyMap (IntegrationCocycleNormalization.smoothFormsToInjectiveHom E M) n
        (CochainClasses.Homology.cochainClass (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) n a
          (IntegrationCocycleNormalization.smoothFormCochain_closed E M n a ha)))).hom =
      Filtered.DerivedInclusion.Hodge.smoothGlobalDerivedClass E M n a ha ≫ (smoothLocallyConstantResolutionIso E M).inv⟦(n : ℤ)⟧' := by
  rw [IntegrationCocycleNormalization.smoothForm_injectiveExt_class E M n a ha]
  have hn : smoothLocallyConstantAugmentation E M ≫
      (IntegrationSheafMap.integrationSheafMap E M ≫ Smooth.SingularInjective.Integration.smoothSingularToInjective E M) =
        (InjectiveExtPullback.complexInjectiveResolution (TopCat.of M)).ι := by
    erw [← Category.assoc, IntegrationSheafMap.integrationSheafMap_augmentation, Smooth.SingularInjective.Integration.smoothSingularToInjective_normalization]
    rfl
  have h := NonnegativeResolutionClasses.Ext.normalizedResolution_extMk_hom (C := ConstantSheafSections.ComplexSheaves (TopCat.of M))
    (smoothLocallyConstantAugmentation E M) (InjectiveExtPullback.complexInjectiveResolution (TopCat.of M))
    (IntegrationSheafMap.integrationSheafMap E M ≫ Smooth.SingularInjective.Integration.smoothSingularToInjective E M) hn n
    (Filtered.DerivedInclusion.Hodge.smoothGlobalCocycle E M n a) (Filtered.DerivedInclusion.Hodge.smoothGlobalCocycle_closed E M n a ha)
  convert h using 1 <;> rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.IntegrationDerivedNormalization
