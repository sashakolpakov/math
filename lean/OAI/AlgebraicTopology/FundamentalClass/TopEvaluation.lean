import OAI.AlgebraicTopology.FundamentalClass.EvaluationLocalization
import OAI.AlgebraicTopology.FundamentalClass.Integration
import OAI.Analysis.DifferentialForms.Manifold.DimensionVanishing

/-! # Top Evaluation -/

namespace OAI.AlgebraicTopology.FundamentalClass.TopEvaluation.IntegrationConstruction

noncomputable section

/-! Actual singular evaluation on the fundamental class, regarded as a
linear functional on top forms. Every top form is closed by dimension. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.FundamentalClass.Integration
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable (d : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]
    [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M]

theorem topForm_closed (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form = 0 :=
  Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.eq_zero_of_finrank_lt (by simp) _

def closedTopForm :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d →ₗ[ℂ] Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (Fin d → ℝ) M d :=
  LinearMap.codRestrict _ LinearMap.id (topForm_closed d M)

def topIntegrationClass :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d →ₗ[ℂ]
      Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) (TopCat.of M) d :=
  (Cohomology.Singular.GlobalSmoothComparison.manifoldSmoothCohomologyIso (Fin d → ℝ) M d).inv.hom.comp
    ((DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCohomologyMap (Fin d → ℝ) M d).hom.comp
      ((Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (Fin d → ℝ) M d).comp (closedTopForm d M)))

theorem topIntegrationClass_restriction (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d) :
    HomologicalComplex.homologyMap
      (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction (Fin d → ℝ) (ModuleCat.of ℂ ℂ) M) d
      (topIntegrationClass d M form) =
      DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCohomologyMap (Fin d → ℝ) M d
        (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (Fin d → ℝ) M d (closedTopForm d M form)) := by
  exact CategoryTheory.Iso.inv_hom_id_apply (Cohomology.Singular.GlobalSmoothComparison.manifoldSmoothCohomologyIso (Fin d → ℝ) M d) _

theorem topIntegrationClass_eq (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (Fin d → ℝ) M d)
    (β : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) (TopCat.of M) d)
    (hβ : HomologicalComplex.homologyMap
      (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction (Fin d → ℝ) (ModuleCat.of ℂ ℂ) M) d β =
      DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCohomologyMap (Fin d → ℝ) M d
        (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (Fin d → ℝ) M d form)) :
    β = topIntegrationClass d M form.val := by
  apply (Cohomology.Singular.GlobalSmoothComparison.manifoldSmoothCohomologyIso (Fin d → ℝ) M d).toLinearEquiv.injective
  exact hβ.trans (topIntegrationClass_restriction d M form.val).symm

variable [T2Space M] [CompactSpace M]

def fundamentalEvaluation (o : IntegrationOrientation.Orientation d M) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d →ₗ[ℂ] ℂ :=
  ((Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℂ ℂ) (TopCat.of M) d).flip (IntegrationOrientation.fundamentalClass o)).comp
    (topIntegrationClass d M)

theorem evaluation_eq_fundamentalEvaluation (o : IntegrationOrientation.Orientation d M)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (Fin d → ℝ) M d)
    (β : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) (TopCat.of M) d)
    (hβ : HomologicalComplex.homologyMap
      (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction (Fin d → ℝ) (ModuleCat.of ℂ ℂ) M) d β =
      DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCohomologyMap (Fin d → ℝ) M d
        (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (Fin d → ℝ) M d form)) :
    Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℂ ℂ) (TopCat.of M) d β (IntegrationOrientation.fundamentalClass o) =
      fundamentalEvaluation d M o form.val := by
  rw [topIntegrationClass_eq d M form β hβ]
  rfl

end

end OAI.AlgebraicTopology.FundamentalClass.TopEvaluation.IntegrationConstruction
