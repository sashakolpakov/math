import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CochainConjugation
import OAI.AlgebraicTopology.DeRham.Comparison.Projective

/-! # Betti Conjugation -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction

noncomputable section

/-! Conjugation on the actual geometric Betti Hodge pieces for HodgeComparison. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff Simplicial

section Manifold

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Conjugation of the genuine integration cocycle represents integration
of the conjugated closed one-form. -/
theorem conjugateIntegrationClass (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 1) :
    CochainConjugation.CM.Construction.conjugateSimplicialH1 (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) 1
          (AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle E M 1 form)) =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) 1
        (AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle E M 1 (Conjugation.CM.Construction.conjugateClosedForm form)) := by
  unfold CochainConjugation.CM.Construction.conjugateSimplicialH1
  rw [CochainConjugation.CM.Construction.semilinearH1Map_class]
  apply congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) 1)
  apply Subtype.ext
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
    (ModuleCat.of ℂ ℂ) 1).toLinearEquiv.injective
  funext sigma
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
    (ModuleCat.of ℂ ℂ) 1).hom
      (CochainConjugation.CM.Construction.conjugateSimplicialCochain _ 1 (AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E M 1 form.val)) sigma =
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
      (ModuleCat.of ℂ ℂ) 1).hom
        (AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E M 1 (Conjugation.CM.Construction.conjugateSmoothForm form.val)) sigma
  rw [CochainConjugation.CM.Construction.conjugateSimplicialCochain_function, AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain_function,
    AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain_function]
  exact (Conjugation.CM.Construction.simplexIntegration_conjugate sigma form.val).symm

end Manifold

/-- Ordinary Betti conjugation is induced by conjugating singular-cochain values. -/
def conjugateBettiH1 (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    V.complexCohomology 1 →ₛₗ[starRingEnd ℂ] V.complexCohomology 1 :=
  CochainConjugation.CM.Construction.conjugateSimplicialH1 (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace V.toOver))

/-- The actual integration comparison commutes with conjugation of closed forms. -/
theorem conjugateBettiH1_formClass (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1) :
    conjugateBettiH1 V ((V.deRhamBettiIso 1).hom (V.deRhamClass 1 form)) =
      (V.deRhamBettiIso 1).hom (V.deRhamClass 1 (Conjugation.CM.Construction.conjugateClosedForm form)) := by
  let : IsIso (V.bettiToSmoothSingular 1) := by
    change IsIso (HomologicalComplex.homologyMap V.bettiRestrictionCochain 1)
    infer_instance
  apply (asIso (V.bettiToSmoothSingular 1)).toLinearEquiv.injective
  change V.bettiToSmoothSingular 1
    (conjugateBettiH1 V ((V.deRhamBettiIso 1).hom (V.deRhamClass 1 form))) =
    V.bettiToSmoothSingular 1
      ((V.deRhamBettiIso 1).hom (V.deRhamClass 1 (Conjugation.CM.Construction.conjugateClosedForm form)))
  have hnat (b : V.complexCohomology 1) :
      V.bettiToSmoothSingular 1 (conjugateBettiH1 V b) =
        CochainConjugation.CM.Construction.conjugateSimplicialH1
          (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex V.analyticModel V.analyticSpace).toSSet
          (V.bettiToSmoothSingular 1 b) :=
    (CochainConjugation.CM.Construction.conjugateSimplicialH1_pullback
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothInclusion V.analyticModel V.analyticSpace) b).symm
  rw [hnat, V.deRhamBettiIso_formClass, conjugateIntegrationClass,
    V.deRhamBettiIso_formClass]

/-- Cochain conjugation sends the geometric (1,0) Betti piece to (0,1). -/
theorem conjugateBettiH1_holomorphic (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : V.complexCohomology 1) (ha : a ∈ V.pureBettiSubspace 1 0) :
    conjugateBettiH1 V a ∈ V.pureBettiSubspace 0 1 := by
  obtain ⟨form, hform, hclass⟩ := (V.mem_pureBettiSubspace_iff 1 0 a).mp ha
  apply (V.mem_pureBettiSubspace_iff 0 1 _).mpr
  refine ⟨Conjugation.CM.Construction.conjugateClosedForm form, Conjugation.CM.Construction.conjugateRawForm_holomorphic form.val.val hform, ?_⟩
  rw [← hclass, conjugateBettiH1_formClass]

/-- Cochain conjugation sends the geometric (0,1) Betti piece to (1,0). -/
theorem conjugateBettiH1_antiholomorphic (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : V.complexCohomology 1) (ha : a ∈ V.pureBettiSubspace 0 1) :
    conjugateBettiH1 V a ∈ V.pureBettiSubspace 1 0 := by
  obtain ⟨form, hform, hclass⟩ := (V.mem_pureBettiSubspace_iff 0 1 a).mp ha
  apply (V.mem_pureBettiSubspace_iff 1 0 _).mpr
  refine ⟨Conjugation.CM.Construction.conjugateClosedForm form, Conjugation.CM.Construction.conjugateRawForm_antiholomorphic form.val.val hform, ?_⟩
  rw [← hclass, conjugateBettiH1_formClass]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction
