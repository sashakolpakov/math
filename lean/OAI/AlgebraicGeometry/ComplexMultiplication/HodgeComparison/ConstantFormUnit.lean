import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NormalizedPrimitives
import OAI.AlgebraicTopology.DeRham.Comparison.Projective
import OAI.AlgebraicTopology.Products.CupCohomologyAlgebra

/-! # Constant Form Unit -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ConstantFormUnit.CM.Construction

noncomputable section

/-! The actual constant-one differential form represents the singular
cup-product unit under canonical integration. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Products.CupCohomologyAlgebra
open scoped _root_.Manifold ContDiff Simplicial

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def constantClosedZeroForm (z : ℂ) : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 0 :=
  ⟨NormalizedPrimitives.CM.Construction.constantZeroForm E M z, NormalizedPrimitives.CM.Construction.constantZeroForm_d E M z⟩

theorem constantOneForm_integration :
    AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle E M 0 (constantClosedZeroForm E M 1) =
      AlgebraicTopology.Products.CupCohomologyAlgebra.cocycleCupUnit (R := ℂ) (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet := by
  apply Subtype.ext
  apply AlgebraicTopology.Products.Cup.cochain_ext _ (ModuleCat.of ℂ ℂ)
  intro sigma
  rw [AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle_evaluation, AlgebraicTopology.DeRham.Comparison.SmoothSimplexAugmentation.smoothSimplexIntegration_zero]
  exact (NormalizedPrimitives.CM.Construction.constantZeroForm_scalar E M 1 _).trans
    (AlgebraicTopology.Products.Cup.evaluation_cupUnit (R := ℂ) (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet sigma).symm

theorem constantOneForm_bettiClass (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    (V.deRhamBettiIso 0).hom
      (V.deRhamClass 0 (constantClosedZeroForm V.analyticModel V.analyticSpace 1)) =
      AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCupUnit (R := ℂ) (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace V.toOver)) := by
  apply (V.deRhamBettiIso_apply_eq_iff 0 _ _).mpr
  rw [V.deRhamToSmoothSingular_formClass, constantOneForm_integration]
  have h := AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality V.bettiRestrictionCochain 0
    (AlgebraicTopology.Products.CupCohomologyAlgebra.cocycleCupUnit (R := ℂ) (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace V.toOver)))
  refine Eq.trans ?_ h.symm
  apply congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass V.smoothSingularComplex 0)
  apply Subtype.ext
  exact (AlgebraicTopology.Products.Cup.cupUnit_pullback (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothInclusion V.analyticModel V.analyticSpace)).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ConstantFormUnit.CM.Construction
