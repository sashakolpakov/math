import OAI.AlgebraicGeometry.Comparison.Betti.GlobalIntegrationSheafification
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.SingularInjective

/-! # Integration Injective Sections -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.IntegrationInjectiveSections

noncomputable section

/-! Integration and ordinary-to-smooth restriction reach the original
injective resolution through the normalized actual sheaf maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def smoothSingularToInjectiveSections :
    AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M ⟶
      (((FlasqueBiproduct.sections (X := TopCat.of M) (⊤ : Opens M)).mapHomologicalComplex (.up ℕ)).obj
        (injectiveResolution (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf (TopCat.of M))).cocomplex) :=
  Smooth.GlobalSheafification.Integration.smoothCochainsToSheafSections E M ≫
    ((FlasqueBiproduct.sections (X := TopCat.of M) (⊤ : Opens M)).mapHomologicalComplex (.up ℕ)).map
      (Smooth.SingularInjective.Integration.smoothSingularToInjective E M)

def smoothFormsToInjectiveSections : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M ⟶
    (((FlasqueBiproduct.sections (X := TopCat.of M) (⊤ : Opens M)).mapHomologicalComplex (.up ℕ)).obj
      (injectiveResolution (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf (TopCat.of M))).cocomplex) :=
  (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamGlobalSectionsIso E M).inv ≫
    ((FlasqueBiproduct.sections (X := TopCat.of M) (⊤ : Opens M)).mapHomologicalComplex (.up ℕ)).map
      (IntegrationSheafMap.integrationSheafMap E M ≫ Smooth.SingularInjective.Integration.smoothSingularToInjective E M)

theorem smoothFormsToInjectiveSections_integration :
    smoothFormsToInjectiveSections E M =
      AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M ≫ smoothSingularToInjectiveSections E M := by
  unfold smoothFormsToInjectiveSections smoothSingularToInjectiveSections
  erw [CategoryTheory.Functor.map_comp, ← Category.assoc,
    GlobalIntegrationSheafification.globalIntegrationSheafification_square, Category.assoc]

theorem singularSmoothInjectiveSections_cohomology
    [StronglyLocallyContractibleSpace M] [MetrizableSpace M] (n : ℕ) :
    HomologicalComplex.homologyMap
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M ≫
        smoothSingularToInjectiveSections E M) n =
      HomologicalComplex.homologyMap (SingularInjective.singularToInjectiveSections (TopCat.of M)) n := by
  unfold smoothSingularToInjectiveSections SingularInjective.singularToInjectiveSections
  erw [← Category.assoc, ← Smooth.GlobalSheafification.Integration.singularSmoothSheafification_square, Category.assoc,
    ← CategoryTheory.Functor.map_comp, HomologicalComplex.homologyMap_comp,
    Smooth.SingularInjective.Integration.singularSmoothToInjective_cohomology]
  exact (HomologicalComplex.homologyMap_comp _ _ n).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.IntegrationInjectiveSections
