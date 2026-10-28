import OAI.AlgebraicGeometry.Comparison.Betti.IntegrationCocycleNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.SingularExtNaturality

/-! # Integrated Singular Ext -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.IntegratedSingularExt.Integration

noncomputable section

/-! A singular class with the same actual smooth-simplex integration image
has the same class in the original locally constant Ext comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] [StronglyLocallyContractibleSpace M] [MetrizableSpace M]

local instance integratedSingularHasDerived : HasDerivedCategory.{1} (ConstantSheafSections.ComplexSheaves (TopCat.of M)) := HasDerivedCategory.standard _
local instance integratedSingularHasExt : HasExt.{1} (ConstantSheafSections.ComplexSheaves (TopCat.of M)) := hasExt_of_hasDerivedCategory _

theorem integratedSingular_ext (n : ℕ) (a : (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M).homology n)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) (TopCat.of M) n)
    (hb : HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M) n b =
      HomologicalComplex.homologyMap (AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M) n a) :
    SingularExtNaturality.singularLocallyConstantExtEquiv (TopCat.of M) n b =
      InjectiveExtPullback.injectiveHomologyExtEquiv (TopCat.of M) n
        (HomologicalComplex.homologyMap (IntegrationCocycleNormalization.smoothFormsToInjectiveHom E M) n a) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℂ) (.up ℕ) n
  have hs := ConcreteCategory.congr_hom (IntegrationInjectiveSections.singularSmoothInjectiveSections_cohomology E M n) b
  have hi := ConcreteCategory.congr_hom
    (congrArg (fun f => HomologicalComplex.homologyMap f n)
      (IntegrationInjectiveSections.smoothFormsToInjectiveSections_integration E M)) a
  simp only [HomologicalComplex.homologyMap_comp, ConcreteCategory.comp_apply] at hs hi
  have he : H.map (SingularInjective.singularToInjectiveSections (TopCat.of M)) b =
      H.map (IntegrationInjectiveSections.smoothFormsToInjectiveSections E M) a := by
    exact hs.symm.trans ((congrArg (H.map (IntegrationInjectiveSections.smoothSingularToInjectiveSections E M)) hb).trans hi.symm)
  change InjectiveExtPullback.injectiveHomologyExtEquiv (TopCat.of M) n
    (H.map (InjectiveHomPullback.injectiveHomSectionsIso (TopCat.of M)).inv
      (H.map (SingularInjective.singularToInjectiveSections (TopCat.of M)) b)) = _
  rw [he]
  unfold IntegrationCocycleNormalization.smoothFormsToInjectiveHom
  erw [HomologicalComplex.homologyMap_comp]
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.IntegratedSingularExt.Integration
