import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverSmooth
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveNaturality
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectivePurePullback

/-! # Analytic Pullback -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AnalyticPullback.CM

noncomputable section

/-! Actual rational pullback and Hodge compatibility for smooth
holomorphic maps between the given projective varieties. These maps need
not be supplied as scheme morphisms: singular pullback and naturality of
the native integration comparison suffice. -/

open scoped Classical _root_.Manifold ContDiff TensorProduct
open _root_.CategoryTheory

variable {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (f : C(X.analyticSpace, Y.analyticSpace))

def pointMap : Betti.Scheme.schemePointSpace X.toOver ⟶ Betti.Scheme.schemePointSpace Y.toOver := TopCat.ofHom f

abbrev pullbackQ (n : ℕ) : Y.rationalCohomology n ⟶ X.rationalCohomology n :=
  AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (pointMap f) n

abbrev pullbackC (n : ℕ) : Y.complexCohomology n ⟶ X.complexCohomology n :=
  AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) (pointMap f) n

theorem complexification_pullback (n : ℕ)
    (x : ComplexMultiplication.WeightOne.CM.Complexification (Y.rationalCohomology n)) :
    ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) n
        ((pullbackQ f n).hom.baseChange ℂ x) =
      pullbackC f n (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace Y.toOver) n x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z c =>
      simp only [LinearMap.baseChange_tmul, ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul]
      exact (congrArg (fun y : X.complexCohomology n => z • y)
        (ConcreteCategory.congr_hom
          (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology_naturality (pointMap f) n) c)).trans
        ((pullbackC f n).hom.map_smul z _).symm
  | add x y hx hy => simp only [map_add, hx, hy]

variable (hf : ContMDiff 𝓘(ℂ, X.analyticModel) 𝓘(ℂ, Y.analyticModel) ∞ f)

include hf

abbrev pullbackDeRham (n : ℕ) : Y.deRhamCohomology n ⟶ X.deRhamCohomology n :=
  Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf) n

/-- The same integration comparison is natural for the actual smooth
map constructed from the covering relation. -/
theorem deRham_naturality (n : ℕ) :
    (Y.deRhamBettiIso n).hom ≫ pullbackC f n =
      pullbackDeRham f hf n ≫ (X.deRhamBettiIso n).hom := by
  exact Betti.CohomologySpan.Realization.cohomologySpanIso_naturality
    Y.deRhamIntegrationCochain Y.bettiRestrictionCochain
    X.deRhamIntegrationCochain X.bettiRestrictionCochain
    (Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf))
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothPullback X.analyticModel Y.analyticModel
      (ModuleCat.of ℂ ℂ) f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf))
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) (pointMap f))
    (AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap_naturality
      f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf)).symm
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothCochainRestriction_naturality (ModuleCat.of ℂ ℂ)
      f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf)).symm n

theorem pullback_mem_pure (p q : ℕ) {a : Y.complexCohomology (p + q)}
    (ha : a ∈ Y.pureBettiSubspace p q) :
    pullbackC f (p + q) a ∈ X.pureBettiSubspace p q := by
  obtain ⟨b, hb, rfl⟩ := ha
  refine ⟨pullbackDeRham f hf (p + q) b, ?_, ?_⟩
  · exact AlgebraicTopology.DeRham.Comparison.ManifoldPureClassesPullback.manifoldDeRhamCohomologyPullback_mem_pureImage f hf p q hb
  · exact (ConcreteCategory.congr_hom (deRham_naturality f hf (p + q)) b).symm

/-- Actual rational pullback is a Hodge map for the canonical structures. -/
theorem pullback_isHodgeMap
    (HX : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (X.rationalCohomology 1))
    (HY : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (Y.rationalCohomology 1))
    (hX : HX.holomorphic = (X.pureBettiSubspace 1 0).comap
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 1))
    (hY : HY.holomorphic = (Y.pureBettiSubspace 1 0).comap
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace Y.toOver) 1)) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap HY HX (pullbackQ f 1).hom := by
  intro x hx
  rw [hX]
  rw [hY] at hx
  change ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 1
    ((pullbackQ f 1).hom.baseChange ℂ x) ∈ X.pureBettiSubspace 1 0
  rw [complexification_pullback]
  exact pullback_mem_pure f hf 1 0 hx

theorem pullback_form_class (n : ℕ) (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms Y.analyticModel Y.analyticSpace n) :
    pullbackC f n ((Y.deRhamBettiIso n).hom (Y.deRhamClass n form)) =
      (X.deRhamBettiIso n).hom (X.deRhamClass n
        (Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf) n form)) := by
  have hn := ConcreteCategory.congr_hom (deRham_naturality f hf n) (Y.deRhamClass n form)
  change pullbackC f n ((Y.deRhamBettiIso n).hom (Y.deRhamClass n form)) =
    (X.deRhamBettiIso n).hom (pullbackDeRham f hf n (Y.deRhamClass n form)) at hn
  rw [hn]
  congr 1
  exact Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldDeRhamFormClass_pullback_apply f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf) n form

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AnalyticPullback.CM
