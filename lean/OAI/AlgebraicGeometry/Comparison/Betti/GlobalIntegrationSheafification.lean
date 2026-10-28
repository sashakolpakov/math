import OAI.AlgebraicGeometry.Comparison.Betti.IntegrationSheafMap
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.GlobalSheafification
import OAI.Analysis.DifferentialForms.Manifold.SheafDeRham

/-! # Global Integration Sheafification -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.GlobalIntegrationSheafification

noncomputable section

/-! Global simplex integration and integration of the actual form sheaf
agree through the original top-section identifications and sheafification. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem integrationSheafSections_factorization :
    ((FlasqueBiproduct.sections (⊤ : Opens M)).mapHomologicalComplex (.up ℕ)).map
        (IntegrationSheafMap.integrationSheafMap E M) =
      (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafSectionsIso E (⊤ : Opens M)).hom ≫
        AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegration E (⊤ : Opens M) ≫
          SectionSheafification.Integration.sectionSheafification (X := TopCat.of M)
            (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ)) ⊤ := by
  apply HomologicalComplex.Hom.ext
  funext n
  change ((AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E M).f n).app (op ⊤) ≫ _ = _
  rw [AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap_f_app]
  exact (Category.id_comp _).symm

theorem globalIntegrationSheafification_square :
    (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamGlobalSectionsIso E M).inv ≫
        ((FlasqueBiproduct.sections (⊤ : Opens M)).mapHomologicalComplex (.up ℕ)).map
          (IntegrationSheafMap.integrationSheafMap E M) =
      AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M ≫ Smooth.GlobalSheafification.Integration.smoothCochainsToSheafSections E M := by
  rw [integrationSheafSections_factorization]
  erw [← Category.assoc, ← Category.assoc]
  change ((Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamTopIso E M).hom ≫ _) ≫ _ = _
  rw [Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamTopIso_hom, AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegration_onOpen]
  unfold Smooth.GlobalSheafification.Integration.smoothCochainsToSheafSections
  rw [AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSections.manifoldSmoothPresheafTopIso_inv]
  exact Category.assoc _ _ _

end

end OAI.AlgebraicGeometry.Comparison.Betti.GlobalIntegrationSheafification
