import OAI.Geometry.ComplexTorus.RiemannProjectivity.TorusCohomology
import OAI.AlgebraicTopology.DeRham.Comparison.Manifold
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass
import OAI.AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison
import OAI.AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange

/-! # Betti De -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.BettiDe.Constructions.Betti

noncomputable section

/-!
# RiemannProjectivity: actual singular cohomology of the CM period torus

The comparison below is the composite of genuine simplex integration and
the inverse of ordinary-to-smooth singular restriction. It is not an
arbitrary vector-space isomorphism. The computed de Rham covectors thereby
give the torus's actual complex singular cohomology.
-/

open _root_.CategoryTheory
open scoped _root_.NumberField ContDiff _root_.Manifold

open OAI.AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM OAI.AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E)

/-- Integration and smooth-singular restriction define the canonical
comparison on the actual compact period manifold. -/
def deRhamBettiEquiv (n : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus n ≃ₗ[ℂ]
      AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) (TopCat.of Φ.periodTorus) n :=
  ((AlgebraicTopology.DeRham.Comparison.Manifold.manifoldDeRhamSmoothCohomologyIso (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus n) ≪≫
    (AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison.manifoldSmoothCohomologyIso (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus n).symm).toLinearEquiv

/-- The computed covector representative gives every complex singular H¹ class. -/
def invariantBettiH1Equiv : (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] ℂ) ≃ₗ[ℂ]
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) (TopCat.of Φ.periodTorus) 1 :=
  (TorusCohomology.Constructions.Torus.invariantH1Equiv Φ).trans (deRhamBettiEquiv Φ 1)

/-- The comparison square uses the actual integration map and the actual
restriction of singular cochains. -/
theorem deRhamBettiEquiv_restriction (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus n) :
    (AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison.manifoldSmoothCohomologyIso (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus n).hom
      (deRhamBettiEquiv Φ n a) =
        AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCohomologyMap (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus n a := by
  change (AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison.manifoldSmoothCohomologyIso (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus n).toLinearEquiv
    ((AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison.manifoldSmoothCohomologyIso (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus n).toLinearEquiv.symm
      ((AlgebraicTopology.DeRham.Comparison.Manifold.manifoldDeRhamSmoothCohomologyIso (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus n).hom a)) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- In particular invariant classes are represented by their literal
integration cocycles on all genuine smooth singular simplices. -/
theorem invariantBettiH1_restriction (l : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] ℂ) :
    (AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison.manifoldSmoothCohomologyIso (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1).hom
      (invariantBettiH1Equiv Φ l) =
        AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (ModuleCat.of ℂ ℂ) Φ.periodTorus) 1
          (AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1
            (FormsEq.Constructions.Forms.invariantClosedOneForm Φ l)) := by
  rw [invariantBettiH1Equiv, LinearEquiv.trans_apply, deRhamBettiEquiv_restriction]
  exact AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCohomologyMap_formClass
    (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1 (FormsEq.Constructions.Forms.invariantClosedOneForm Φ l)

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.BettiDe.Constructions.Betti
