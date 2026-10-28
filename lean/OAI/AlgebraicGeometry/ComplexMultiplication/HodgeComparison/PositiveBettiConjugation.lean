import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PositiveCohomologyConjugation
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BettiConjugation

/-! # Positive Betti Conjugation -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PositiveBettiConjugation.CM.Construction

noncomputable section

/-! The canonical de Rham–Betti comparison commutes with actual
conjugation in every positive degree. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff Simplicial

theorem conjugateIntegrationSuccClass (E M : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (n : ℕ) (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M (n + 1)) :
    PositiveCohomologyConjugation.CM.Construction.conjugateSimplicialHSucc (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet n
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) (n + 1)
        (AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle E M (n + 1) form)) =
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) (n + 1)
      (AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle E M (n + 1) (Conjugation.CM.Construction.conjugateClosedForm form)) := by
  unfold PositiveCohomologyConjugation.CM.Construction.conjugateSimplicialHSucc
  rw [PositiveCohomologyConjugation.CM.Construction.semilinearHSuccMap_class]
  apply congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) (n + 1))
  apply Subtype.ext
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
    (ModuleCat.of ℂ ℂ) (n + 1)).toLinearEquiv.injective
  funext sigma
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
    (ModuleCat.of ℂ ℂ) (n + 1)).hom
      (CochainConjugation.CM.Construction.conjugateSimplicialCochain _ (n + 1) (AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E M (n + 1) form.val)) sigma =
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
      (ModuleCat.of ℂ ℂ) (n + 1)).hom
        (AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E M (n + 1) (Conjugation.CM.Construction.conjugateSmoothForm form.val)) sigma
  rw [CochainConjugation.CM.Construction.conjugateSimplicialCochain_function, AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain_function, AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain_function]
  exact (Conjugation.CM.Construction.simplexIntegration_conjugate sigma form.val).symm

def conjugateBettiHSucc (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    V.complexCohomology (n + 1) →ₛₗ[starRingEnd ℂ] V.complexCohomology (n + 1) :=
  PositiveCohomologyConjugation.CM.Construction.conjugateSimplicialHSucc (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace V.toOver)) n

theorem conjugateBettiHSucc_formClass (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace (n + 1)) :
    conjugateBettiHSucc V n ((V.deRhamBettiIso (n + 1)).hom (V.deRhamClass (n + 1) form)) =
      (V.deRhamBettiIso (n + 1)).hom (V.deRhamClass (n + 1) (Conjugation.CM.Construction.conjugateClosedForm form)) := by
  let : IsIso (V.bettiToSmoothSingular (n + 1)) := by
    change IsIso (HomologicalComplex.homologyMap V.bettiRestrictionCochain (n + 1))
    infer_instance
  apply (asIso (V.bettiToSmoothSingular (n + 1))).toLinearEquiv.injective
  change V.bettiToSmoothSingular (n + 1)
    (conjugateBettiHSucc V n ((V.deRhamBettiIso (n + 1)).hom (V.deRhamClass (n + 1) form))) =
    V.bettiToSmoothSingular (n + 1)
      ((V.deRhamBettiIso (n + 1)).hom (V.deRhamClass (n + 1) (Conjugation.CM.Construction.conjugateClosedForm form)))
  have hnat (b : V.complexCohomology (n + 1)) :
      V.bettiToSmoothSingular (n + 1) (conjugateBettiHSucc V n b) =
        PositiveCohomologyConjugation.CM.Construction.conjugateSimplicialHSucc
          (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex V.analyticModel V.analyticSpace).toSSet n
          (V.bettiToSmoothSingular (n + 1) b) :=
    (PositiveCohomologyConjugation.CM.Construction.conjugateSimplicialHSucc_pullback
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothInclusion V.analyticModel V.analyticSpace) n b).symm
  rw [hnat, V.deRhamBettiIso_formClass, conjugateIntegrationSuccClass, V.deRhamBettiIso_formClass]

theorem rational_formClass_conjugate (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (a : V.rationalCohomology (n + 1))
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace (n + 1))
    (hform : (V.deRhamBettiIso (n + 1)).hom (V.deRhamClass (n + 1) form) =
      V.rationalCohomologyInclusion (n + 1) a) :
    (V.deRhamBettiIso (n + 1)).hom (V.deRhamClass (n + 1) (Conjugation.CM.Construction.conjugateClosedForm form)) =
      V.rationalCohomologyInclusion (n + 1) a := by
  rw [← conjugateBettiHSucc_formClass, hform]
  exact PositiveCohomologyConjugation.CM.Construction.conjugateSimplicialHSucc_rational (Betti.Scheme.schemePointSpace V.toOver) n a

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PositiveBettiConjugation.CM.Construction
