import OAI.AlgebraicTopology.FundamentalClass.SupportedEvaluation

/-! # Evaluation Localization -/

namespace OAI.AlgebraicTopology.FundamentalClass.EvaluationLocalization.IntegrationConstruction

noncomputable section

/-! The ordinary singular evaluation can be computed on any smooth relative
cycle representing its restriction to the support of the form. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem evaluation_smooth_cycle (n : ℕ) (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n)
    (β : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) (TopCat.of M) n)
    (hβ : HomologicalComplex.homologyMap
      (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M) n β =
        DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCohomologyMap E M n (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M n form))
    (c : Cohomology.Singular.ChainRepresentatives.chainCycles (SmoothHomology.IntegrationConstruction.smoothChains E M) n) :
    Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℂ ℂ) (TopCat.of M) n β
      (HomologicalComplex.homologyMap (SmoothHomology.IntegrationConstruction.smoothChainInclusion E M) n
        (Cohomology.Singular.ChainRepresentatives.chainClass (SmoothHomology.IntegrationConstruction.smoothChains E M) n c)) =
      SupportedEvaluation.IntegrationConstruction.smoothIntegrationFunctional E M n form.val c.val := by
  refine (Cohomology.Singular.EvaluationNaturality.simplicialHomologyEvaluation_naturality (ModuleCat.of ℂ ℂ)
    (Cohomology.Singular.ManifoldSmooth.manifoldSmoothInclusion E M) n β (Cohomology.Singular.ChainRepresentatives.chainClass (SmoothHomology.IntegrationConstruction.smoothChains E M) n c)).symm.trans ?_
  change Cohomology.Singular.Evaluation.simplicialHomologyEvaluation (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
    (ModuleCat.of ℂ ℂ) n
    (HomologicalComplex.homologyMap
      (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M) n β)
    (Cohomology.Singular.ChainRepresentatives.chainClass (SmoothHomology.IntegrationConstruction.smoothChains E M) n c) = _
  rw [hβ, DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCohomologyMap_formClass,
    Cohomology.Singular.Evaluation.simplicialHomologyEvaluation_class_class]
  rfl

theorem evaluation_eq_relativeIntegration (U : Opens M) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n) (hform : ∀ x : U, form.val.val x = 0)
    (β : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) (TopCat.of M) n)
    (hβ : HomologicalComplex.homologyMap
      (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M) n β =
        DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCohomologyMap E M n (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M n form))
    (z : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℂ) (TopCat.of M)).homology n)
    (a : (RelativeSmooth.IntegrationConstruction.smoothRelativeChains E M U).homology n)
    (ha : HomologicalComplex.homologyMap (RelativeSmooth.IntegrationConstruction.smoothRelativeComparison E M U) n a =
      HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℂ (TopCat.of M) U) n z) :
    Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℂ ℂ) (TopCat.of M) n β z =
      SupportedEvaluation.IntegrationConstruction.relativeIntegrationOnHomology E M U n form hform a := by
  obtain ⟨c, rfl⟩ := SmoothHomology.IntegrationConstruction.exists_smooth_cycle_representative E M n z
  have heq : a = HomologicalComplex.homologyMap (RelativeSmooth.IntegrationConstruction.smoothRelativeProjection E M U) n
      (Cohomology.Singular.ChainRepresentatives.chainClass (SmoothHomology.IntegrationConstruction.smoothChains E M) n c) := by
    apply RelativeSmooth.IntegrationConstruction.smoothRelativeHomologyComparison_injective E M U n
    rw [ha]
    have h := congrArg (fun f => HomologicalComplex.homologyMap f n)
      (RelativeSmooth.IntegrationConstruction.smoothRelativeComparison_projection E M U)
    simp only [HomologicalComplex.homologyMap_comp] at h
    exact (ConcreteCategory.congr_hom h (Cohomology.Singular.ChainRepresentatives.chainClass (SmoothHomology.IntegrationConstruction.smoothChains E M) n c)).symm
  rw [evaluation_smooth_cycle E M n form β hβ c, heq, Cohomology.Singular.EvaluationNaturality.chainClass_naturality]
  exact (SupportedEvaluation.IntegrationConstruction.relativeIntegrationOnHomology_projection_class E M U n form hform c.val
    (Cohomology.Singular.EvaluationNaturality.chainCycleMap (RelativeSmooth.IntegrationConstruction.smoothRelativeProjection E M U) n c).property).symm

theorem evaluation_eq_relative_cycle_integral (U : Opens M) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n) (hform : ∀ x : U, form.val.val x = 0)
    (β : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) (TopCat.of M) n)
    (hβ : HomologicalComplex.homologyMap
      (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M) n β =
        DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCohomologyMap E M n (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M n form))
    (z : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℂ) (TopCat.of M)).homology n)
    (s : (SmoothHomology.IntegrationConstruction.smoothChains E M).X n)
    (hs : (RelativeSmooth.IntegrationConstruction.smoothRelativeProjection E M U).f n s ∈ Cohomology.Singular.ChainRepresentatives.chainCycles (RelativeSmooth.IntegrationConstruction.smoothRelativeChains E M U) n)
    (hclass : HomologicalComplex.homologyMap (RelativeSmooth.IntegrationConstruction.smoothRelativeComparison E M U) n
        (Cohomology.Singular.ChainRepresentatives.chainClass (RelativeSmooth.IntegrationConstruction.smoothRelativeChains E M U) n ⟨(RelativeSmooth.IntegrationConstruction.smoothRelativeProjection E M U).f n s, hs⟩) =
      HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℂ (TopCat.of M) U) n z) :
    Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℂ ℂ) (TopCat.of M) n β z =
      SupportedEvaluation.IntegrationConstruction.smoothIntegrationFunctional E M n form.val s := by
  rw [evaluation_eq_relativeIntegration E M U n form hform β hβ z _ hclass]
  exact SupportedEvaluation.IntegrationConstruction.relativeIntegrationOnHomology_projection_class E M U n form hform s hs

end

end OAI.AlgebraicTopology.FundamentalClass.EvaluationLocalization.IntegrationConstruction
