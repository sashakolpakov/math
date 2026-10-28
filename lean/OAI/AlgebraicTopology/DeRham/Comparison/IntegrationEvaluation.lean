import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration
import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldCechAugmentationBridge
import OAI.AlgebraicTopology.DeRham.Comparison.CechColumns
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSections

/-! # Integration Evaluation -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.IntegrationEvaluation

noncomputable section

/-!
# Evaluation of the actual integration map

Evaluating the integration morphism of presheaf complexes on an open domain
gives its actual open-domain integration map. The source and target
identifications are the previously constructed identity-component section
isomorphisms. This also identifies the maps used on Čech intersections.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSections
open scoped _root_.Manifold ContDiff

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual section identifications intertwine evaluated integration
with integration on the open domain. -/
theorem manifoldOpenIntegrationEvaluation_eq (W : Opens M) :
    (ManifoldCechAugmentationBridge.manifoldPresheafSectionsIso E M W).hom ≫ ManifoldOpenIntegration.manifoldOpenIntegration E W =
      CechComplexAugmentation.presheafComplexSectionsMap W (ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E M) ≫
        (Cohomology.Singular.ManifoldSmoothSections.manifoldSmoothPresheafSectionsIso E M (ModuleCat.of ℂ ℂ) W).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (𝟙 _) ≫ (ManifoldOpenIntegration.manifoldOpenIntegration E W).f n =
    (ManifoldOpenIntegration.manifoldOpenIntegration E W).f n ≫ 𝟙 _
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  rfl

/-- Evaluation of the presheaf integration morphism is isomorphic to the
actual open-domain integration morphism as an arrow of cochain complexes. -/
def manifoldOpenIntegrationEvaluationArrowIso (W : Opens M) :
    Arrow.mk (CechComplexAugmentation.presheafComplexSectionsMap W (ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E M)) ≅
      Arrow.mk (ManifoldOpenIntegration.manifoldOpenIntegration E W) :=
  Arrow.isoMk (ManifoldCechAugmentationBridge.manifoldPresheafSectionsIso E M W)
    (Cohomology.Singular.ManifoldSmoothSections.manifoldSmoothPresheafSectionsIso E M (ModuleCat.of ℂ ℂ) W)
    (manifoldOpenIntegrationEvaluation_eq E M W)

/-- The quasi-isomorphism property of evaluated integration is exactly
the quasi-isomorphism property of the actual integration map. -/
theorem manifoldOpenIntegrationPresheafMap_quasiIso_iff (W : Opens M) :
    QuasiIso (CechComplexAugmentation.presheafComplexSectionsMap W (ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E M)) ↔
      QuasiIso (ManifoldOpenIntegration.manifoldOpenIntegration E W) :=
  quasiIso_iff_of_arrow_mk_iso _ _ (manifoldOpenIntegrationEvaluationArrowIso E M W)

variable {ι : Type} (U : ι → Opens M)

/-- The map on each Čech intersection is the actual integration map on
that intersection, under its genuine section identifications. -/
def manifoldOpenIntegrationIntersectionArrowIso {p : ℕ} (a : Fin (p + 1) → ι) :
    Arrow.mk (CechColumns.cechIntersectionMap U (ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E M) a) ≅
      Arrow.mk (ManifoldOpenIntegration.manifoldOpenIntegration E (SmoothCech.cechIntersection U a)) :=
  manifoldOpenIntegrationEvaluationArrowIso E M (SmoothCech.cechIntersection U a)

/-- Local integration quasi-isomorphisms transfer to exactly the
intersection maps required by Čech descent, in both directions. -/
theorem manifoldOpenIntegrationIntersection_quasiIso_iff {p : ℕ}
    (a : Fin (p + 1) → ι) :
    QuasiIso (CechColumns.cechIntersectionMap U (ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E M) a) ↔
      QuasiIso (ManifoldOpenIntegration.manifoldOpenIntegration E (SmoothCech.cechIntersection U a)) :=
  quasiIso_iff_of_arrow_mk_iso _ _ (manifoldOpenIntegrationIntersectionArrowIso E M U a)

end

end OAI.AlgebraicTopology.DeRham.Comparison.IntegrationEvaluation
