import OAI.AlgebraicTopology.DeRham.Comparison.EuclideanFormCech
import OAI.AlgebraicTopology.DeRham.Comparison.CechTotal
import OAI.AlgebraicTopology.DeRham.Comparison.ConvexSimplexIntegration
import OAI.AlgebraicTopology.DeRham.Comparison.IntegrationEvaluation

/-! # Euclidean Integration Descent -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.EuclideanIntegrationDescent

noncomputable section

/-!
# Actual integration comparison on a convex Čech family

The proved local integration theorem makes the actual Čech total map a
quasi-isomorphism. Together with the proved form augmentation, this reduces
the global comparison to the corresponding smooth singular augmentation.
The latter is kept explicit here and discharged in the global application.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type} (U : ι → Opens E)

/-- Actual integration gives a quasi-isomorphism of Čech totals for every
convex open family, including families with empty intersections. -/
theorem manifoldOpenIntegration_total_quasiIso_of_convex_family
    (hU : ∀ i, Convex ℝ (U i : Set E)) :
    QuasiIso (CechTotalFunctor.cechTotalMap U (ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E E)) := by
  apply CechTotal.cechTotalMap_quasiIso_of_intersections
  intro p a
  exact (IntegrationEvaluation.manifoldOpenIntegrationIntersection_quasiIso_iff E E U a).mpr
    (ConvexSimplexIntegration.manifoldOpenIntegration_quasiIso_convex E _ (Cohomology.Singular.ConvexResolution.convex_cechIntersection U hU a))

/-- The actual integration map descends from a convex cover once the actual
smooth singular augmentation is known to be a quasi-isomorphism. -/
theorem manifoldOpenIntegration_quasiIso_of_convex_cover (W : Opens E)
    (hsub : ∀ i, U i ≤ W) (hcover : ∀ x : W, ∃ i, (x : E) ∈ U i)
    (hU : ∀ i, Convex ℝ (U i : Set E))
    (hTarget : QuasiIso (CechComplexAugmentation.cechTotalAugmentation U W hsub
      (Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E E (ModuleCat.of ℂ ℂ)))) :
    QuasiIso (ManifoldOpenIntegration.manifoldOpenIntegration E W) := by
  apply (IntegrationEvaluation.manifoldOpenIntegrationPresheafMap_quasiIso_iff E E W).mp
  exact CechComplexAugmentation.cechTotalAugmentation_quasiIso_descent U W hsub
    (ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E E)
    (EuclideanFormCech.euclideanManifoldCechAugmentation_quasiIso E U W hsub hcover) hTarget
    (manifoldOpenIntegration_total_quasiIso_of_convex_family E U hU)

end

end OAI.AlgebraicTopology.DeRham.Comparison.EuclideanIntegrationDescent
