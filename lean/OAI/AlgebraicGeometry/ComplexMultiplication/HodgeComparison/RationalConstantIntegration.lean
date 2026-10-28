import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectivePhaseDefect
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalSmoothCochains
import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration

/-! # Rational Constant Integration -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalConstantIntegration.CM.Construction

noncomputable section

/-! Actual integration sends rational locally constant zero-forms to the
literal rational singular augmentation followed by coefficient inclusion. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration
open scoped _root_.Manifold ContDiff Simplicial

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

theorem rationalLocallyConstantManifoldForm_integration
    (U : Opens M) (f : LocallyConstant U ℚ) :
    (AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegration E U).f 0 (ProjectivePhaseDefect.CM.Construction.rationalLocallyConstantManifoldForm (E := E) U f) =
      RationalSmoothCochains.CM.Construction.rationalSmoothCochain E U 0
        (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero (ModuleCat.of ℚ ℚ) (TopCat.of U) f) := by
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet
    (ModuleCat.of ℂ ℂ) 0).toLinearEquiv.injective
  funext sigma
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet
    (ModuleCat.of ℂ ℂ) 0).hom _ sigma =
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet
      (ModuleCat.of ℂ ℂ) 0).hom _ sigma
  let fC : LocallyConstant U ℂ :=
    ⟨fun x => (f x : ℂ), f.isLocallyConstant.comp (fun q : ℚ => (q : ℂ))⟩
  have hI := (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet (ModuleCat.of ℂ ℂ)
    ((AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegration E U).f 0 (ProjectivePhaseDefect.CM.Construction.rationalLocallyConstantManifoldForm (E := E) U f)) sigma).trans
    ((AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegration_evaluation E U 0 _ sigma).trans
      (AlgebraicTopology.DeRham.Comparison.SmoothSimplexAugmentation.smoothSimplexIntegration_locallyConstant_open U fC sigma))
  refine hI.trans ?_
  change (f (TopCat.toSSetObj₀Equiv sigma.val) : ℂ) =
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet
      (ModuleCat.of ℂ ℂ) 0).hom
        ((AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothInclusion E U)).f 0
          ((PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain (TopCat.of U)).f 0
            (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero (ModuleCat.of ℚ ℚ) (TopCat.of U) f))) sigma
  let cQ : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)).X 0 :=
    AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero (ModuleCat.of ℚ ℚ) (TopCat.of U) f
  let cC : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) (TopCat.of U)).X 0 :=
    (PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain (TopCat.of U)).f 0 cQ
  have hR := AlgebraicTopology.Cohomology.Singular.Formulas.degreewiseFunctionIso_pullback (ModuleCat.of ℂ ℂ)
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothInclusion E U) cC sigma
  have hC := AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply (TopCat.toSSet.obj (TopCat.of U))
    (ModuleCat.of ℂ ℂ) cC sigma.val
  have hQ := PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain_evaluation (TopCat.of U) 0 cQ sigma.val
  have hval : AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj (TopCat.of U))
      (ModuleCat.of ℚ ℚ) sigma.val cQ = f (TopCat.toSSetObj₀Equiv sigma.val) := by
    rw [← AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply, ← AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_apply_simplex]
    exact AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero_apply (ModuleCat.of ℚ ℚ) (TopCat.of U) f _
  exact (hR.trans (hC.trans (hQ.trans (congrArg (fun q : ℚ => (q : ℂ)) hval)))).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalConstantIntegration.CM.Construction
