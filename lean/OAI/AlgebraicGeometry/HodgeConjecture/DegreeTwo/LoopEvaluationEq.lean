import OAI.AlgebraicTopology.DeRham.Comparison.Projective
import OAI.AlgebraicTopology.Cohomology.Singular.Formulas

/-! # Loop Evaluation Eq -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LoopEvaluationEq.Constructions.LoopEvaluation

noncomputable section

/-!
# DegreeTwo: actual Betti classes evaluated on smooth loops

A singular coboundary has zero value on a one-simplex whose endpoints agree.
Thus the integration-normalized de Rham comparison determines the value of any
representing singular cocycle on every genuine smooth singular loop.
-/

open _root_.CategoryTheory
open scoped Simplicial

open OAI.AlgebraicTopology.Cohomology.Singular.Formulas

/-- Cohomologous one-cocycles agree on every one-simplex with equal endpoints. -/
theorem cocycle_evaluation_eq {R : Type} [Ring R] (K : SSet.{0}) (M : ModuleCat.{0} R)
    (a b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains K M) 1)
    (hab : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains K M) 1 a =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains K M) 1 b)
    (s : K _⦋1⦌) (hs : K.δ 0 s = K.δ 1 s) :
    AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation K M s a.val = AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation K M s b.val := by
  obtain ⟨c, hc⟩ := (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_iff_exists_succ (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains K M) 0 a b).mp hab
  have h := congrArg (fun d => AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation K M s d) hc
  rw [AlgebraicTopology.Cohomology.Singular.Formulas.evaluation_coboundary_apply, map_sub] at h
  have hz : (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) •
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation K M (K.δ i s) c) = 0 := by
    simp [Fin.sum_univ_two, hs]
  rw [hz] at h
  exact sub_eq_zero.mp h.symm

/-- A Betti cocycle representing a closed form evaluates on a smooth loop
as the literal signed Duffy integral of that form. -/
theorem betti_form_evaluation (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms X.analyticModel X.analyticSpace 1)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℂ ℂ) (TopCat.of X.analyticSpace) 1)
    (hc : AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℂ ℂ) (TopCat.of X.analyticSpace) 1 c =
      (X.deRhamBettiIso 1).hom (X.deRhamClass 1 form))
    (s : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex X.analyticModel X.analyticSpace).toSSet _⦋1⦌)
    (hs : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex X.analyticModel X.analyticSpace).toSSet.δ 0 s =
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex X.analyticModel X.analyticSpace).toSSet.δ 1 s) :
    AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj (TopCat.of X.analyticSpace))
      (ModuleCat.of ℂ ℂ) s.val c.val = AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration s form.val := by
  let cr := AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap X.bettiRestrictionCochain 1 c
  have hclass : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass X.smoothSingularComplex 1 cr =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass X.smoothSingularComplex 1
        (AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle X.analyticModel X.analyticSpace 1 form) := by
    rw [← AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality X.bettiRestrictionCochain 1 c]
    change X.bettiToSmoothSingular 1
      (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℂ ℂ) (TopCat.of X.analyticSpace) 1 c) = _
    rw [hc, X.deRhamBettiIso_formClass]
  have h := cocycle_evaluation_eq _ (ModuleCat.of ℂ ℂ) cr
    (AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle X.analyticModel X.analyticSpace 1 form) hclass s hs
  rw [AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle_evaluation] at h
  change AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation _ (ModuleCat.of ℂ ℂ) s
      ((AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ)
        (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothInclusion X.analyticModel X.analyticSpace)).f 1 c.val) = _ at h
  rw [AlgebraicTopology.Cohomology.Singular.Formulas.evaluation_pullback_apply] at h
  exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LoopEvaluationEq.Constructions.LoopEvaluation
