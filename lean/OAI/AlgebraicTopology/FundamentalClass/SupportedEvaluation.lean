import OAI.AlgebraicTopology.FundamentalClass.RelativeSmooth
import OAI.AlgebraicTopology.FundamentalClass.LinearDescent
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass

/-! # Supported Evaluation -/

namespace OAI.AlgebraicTopology.FundamentalClass.SupportedEvaluation.IntegrationConstruction

noncomputable section

/-! Integration: a closed form vanishing on an open set evaluates on the genuine
relative smooth homology of that pair. This descends the already constructed
simplex integrals, with Stokes supplying the boundary relation. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def smoothIntegrationFunctional (n : ℕ) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    (SmoothHomology.IntegrationConstruction.smoothChains E M).X n →ₗ[ℂ] ℂ :=
  Cohomology.Singular.ChainDual.degreewiseChainDualEquiv (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
    (ModuleCat.of ℂ ℂ) n (DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E M n form)

theorem smoothIntegrationFunctional_boundary (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n) (i : ℕ) (z : (SmoothHomology.IntegrationConstruction.smoothChains E M).X i) :
    smoothIntegrationFunctional E M n form.val ((SmoothHomology.IntegrationConstruction.smoothChains E M).d i n z) = 0 :=
  Cohomology.Singular.Evaluation.cocycle_evaluation_boundary (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
    (ModuleCat.of ℂ ℂ) n i (DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle E M n form) z

theorem pullback_zero_on_open (U : Opens M) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) (hform : ∀ x : U, form.val x = 0) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (Subtype.val : U → M) contMDiff_subtype_val form = 0 := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  change (form.val x).compContinuousLinearMap _ = 0
  rw [hform x]
  rfl

theorem smoothIntegrationFunctional_open (U : Opens M) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) (hform : ∀ x : U, form.val x = 0)
    (z : (SmoothHomology.IntegrationConstruction.smoothChains E U).X n) :
    smoothIntegrationFunctional E M n form ((RelativeSmooth.IntegrationConstruction.smoothOpenChainInclusion E M U).f n z) = 0 := by
  have he : (smoothIntegrationFunctional E M n form).comp
      ((RelativeSmooth.IntegrationConstruction.smoothOpenChainInclusion E M U).f n).hom = 0 := by
    apply Cohomology.Singular.ChainDual.chainFunctional_ext (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet (ModuleCat.of ℂ ℂ)
    intro σ
    change smoothIntegrationFunctional E M n form
      ((Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℂ) (RelativeSmooth.IntegrationConstruction.smoothOpenMap E M U)).f n
        (Cohomology.Singular.ChainDual.simplexChain (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet σ)) = 0
    rw [Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap_simplex]
    unfold smoothIntegrationFunctional
    rw [Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex, DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain_evaluation]
    change DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration
      ((Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothSingularMap E E (Subtype.val : U → M) contMDiff_subtype_val).app _ σ) form = 0
    rw [DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration_postcompose,
      pullback_zero_on_open E M U n form hform, map_zero]
  exact LinearMap.congr_fun he z

theorem smoothIntegrationFunctional_vanishes_kernel (U : Opens M) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) (hform : ∀ x : U, form.val x = 0) :
    LinearMap.ker ((RelativeSmooth.IntegrationConstruction.smoothRelativeProjection E M U).f n).hom ≤
      LinearMap.ker (smoothIntegrationFunctional E M n form) := by
  rw [RelativeSmooth.IntegrationConstruction.smoothRelativeProjection_ker]
  rintro _ ⟨z, rfl⟩
  exact smoothIntegrationFunctional_open E M U n form hform z

def relativeIntegrationFunctional (U : Opens M) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) (hform : ∀ x : U, form.val x = 0) :
    (RelativeSmooth.IntegrationConstruction.smoothRelativeChains E M U).X n →ₗ[ℂ] ℂ :=
  LinearDescent.IntegrationConstruction.factorFunctional ((RelativeSmooth.IntegrationConstruction.smoothRelativeProjection E M U).f n).hom
    (RelativeSmooth.IntegrationConstruction.smoothRelativeProjection_surjective E M U n) (smoothIntegrationFunctional E M n form)
    (smoothIntegrationFunctional_vanishes_kernel E M U n form hform)

theorem relativeIntegrationFunctional_projection (U : Opens M) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) (hform : ∀ x : U, form.val x = 0)
    (z : (SmoothHomology.IntegrationConstruction.smoothChains E M).X n) :
    relativeIntegrationFunctional E M U n form hform ((RelativeSmooth.IntegrationConstruction.smoothRelativeProjection E M U).f n z) =
      smoothIntegrationFunctional E M n form z :=
  LinearDescent.IntegrationConstruction.factorFunctional_apply _ _ _ _ z

theorem relativeIntegrationFunctional_boundary (U : Opens M) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n) (hform : ∀ x : U, form.val.val x = 0)
    (i : ℕ) (z : (RelativeSmooth.IntegrationConstruction.smoothRelativeChains E M U).X i) :
    relativeIntegrationFunctional E M U n form.val hform
      ((RelativeSmooth.IntegrationConstruction.smoothRelativeChains E M U).d i n z) = 0 := by
  obtain ⟨z, rfl⟩ := RelativeSmooth.IntegrationConstruction.smoothRelativeProjection_surjective E M U i z
  have h := ConcreteCategory.congr_hom ((RelativeSmooth.IntegrationConstruction.smoothRelativeProjection E M U).comm i n) z
  change (RelativeSmooth.IntegrationConstruction.smoothRelativeChains E M U).d i n ((RelativeSmooth.IntegrationConstruction.smoothRelativeProjection E M U).f i z) =
    (RelativeSmooth.IntegrationConstruction.smoothRelativeProjection E M U).f n ((SmoothHomology.IntegrationConstruction.smoothChains E M).d i n z) at h
  rw [h, relativeIntegrationFunctional_projection]
  exact smoothIntegrationFunctional_boundary E M n form i z

def relativeIntegrationOnHomology (U : Opens M) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n) (hform : ∀ x : U, form.val.val x = 0) :
    (RelativeSmooth.IntegrationConstruction.smoothRelativeChains E M U).homology n →ₗ[ℂ] ℂ :=
  LinearDescent.IntegrationConstruction.chainFunctionalOnHomology _ n (relativeIntegrationFunctional E M U n form.val hform)
    (relativeIntegrationFunctional_boundary E M U n form hform)

theorem relativeIntegrationOnHomology_projection_class (U : Opens M) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n) (hform : ∀ x : U, form.val.val x = 0)
    (z : (SmoothHomology.IntegrationConstruction.smoothChains E M).X n)
    (hz : (RelativeSmooth.IntegrationConstruction.smoothRelativeProjection E M U).f n z ∈ Cohomology.Singular.ChainRepresentatives.chainCycles (RelativeSmooth.IntegrationConstruction.smoothRelativeChains E M U) n) :
    relativeIntegrationOnHomology E M U n form hform
      (Cohomology.Singular.ChainRepresentatives.chainClass (RelativeSmooth.IntegrationConstruction.smoothRelativeChains E M U) n ⟨(RelativeSmooth.IntegrationConstruction.smoothRelativeProjection E M U).f n z, hz⟩) =
      smoothIntegrationFunctional E M n form.val z := by
  rw [relativeIntegrationOnHomology, LinearDescent.IntegrationConstruction.chainFunctionalOnHomology_class]
  exact relativeIntegrationFunctional_projection E M U n form.val hform z

end

end OAI.AlgebraicTopology.FundamentalClass.SupportedEvaluation.IntegrationConstruction
