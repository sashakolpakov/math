import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicForms
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.TorusRealManifold
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.Torus
import OAI.AlgebraicTopology.DeRham.Comparison.Manifold
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass
import OAI.AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison
import OAI.AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange

/-! # Algebraic Betti -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicBetti.CM.Abelian.Algebraization.Betti

noncomputable section

/-!
# CMAbelianVariety: actual singular cohomology of the generic period torus

The comparison below is the composite of genuine simplex integration and
the inverse of ordinary-to-smooth singular restriction. It is not an
arbitrary vector-space isomorphism. The computed de Rham covectors thereby
give the torus's actual complex singular cohomology.
-/

open _root_.CategoryTheory
open scoped _root_.NumberField ContDiff _root_.Manifold

open OAI.AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM OAI.AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison

variable (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData)

/-- Integration and smooth-singular restriction define the canonical
comparison on the actual compact period manifold. -/
def deRhamBettiEquiv (n : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology (Φ.space) Φ.periodTorus n ≃ₗ[ℂ]
      AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) (TopCat.of Φ.periodTorus) n :=
  ((AlgebraicTopology.DeRham.Comparison.Manifold.manifoldDeRhamSmoothCohomologyIso (Φ.space) Φ.periodTorus n) ≪≫
    (AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison.manifoldSmoothCohomologyIso (Φ.space) Φ.periodTorus n).symm).toLinearEquiv

/-- The computed covector representative gives every complex singular H¹ class. -/
def invariantBettiH1Equiv : (Φ.space →L[ℝ] ℂ) ≃ₗ[ℂ]
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) (TopCat.of Φ.periodTorus) 1 :=
  (Torus.CM.Abelian.Algebraization.invariantH1Equiv Φ).trans (deRhamBettiEquiv Φ 1)

/-- The comparison square uses the actual integration map and the actual
restriction of singular cochains. -/
theorem deRhamBettiEquiv_restriction (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology (Φ.space) Φ.periodTorus n) :
    (AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison.manifoldSmoothCohomologyIso (Φ.space) Φ.periodTorus n).hom
      (deRhamBettiEquiv Φ n a) =
        AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCohomologyMap (Φ.space) Φ.periodTorus n a := by
  change (AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison.manifoldSmoothCohomologyIso (Φ.space) Φ.periodTorus n).toLinearEquiv
    ((AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison.manifoldSmoothCohomologyIso (Φ.space) Φ.periodTorus n).toLinearEquiv.symm
      ((AlgebraicTopology.DeRham.Comparison.Manifold.manifoldDeRhamSmoothCohomologyIso (Φ.space) Φ.periodTorus n).hom a)) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- In particular invariant classes are represented by their literal
integration cocycles on all genuine smooth singular simplices. -/
theorem invariantBettiH1_restriction (l : Φ.space →L[ℝ] ℂ) :
    (AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison.manifoldSmoothCohomologyIso (Φ.space) Φ.periodTorus 1).hom
      (invariantBettiH1Equiv Φ l) =
        AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains (Φ.space) (ModuleCat.of ℂ ℂ) Φ.periodTorus) 1
          (AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle (Φ.space) Φ.periodTorus 1
            (AlgebraicForms.CM.Abelian.Algebraization.Forms.invariantClosedOneForm Φ l)) := by
  rw [invariantBettiH1Equiv, LinearEquiv.trans_apply, deRhamBettiEquiv_restriction]
  exact AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCohomologyMap_formClass
    (Φ.space) Φ.periodTorus 1 (AlgebraicForms.CM.Abelian.Algebraization.Forms.invariantClosedOneForm Φ l)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicBetti.CM.Abelian.Algebraization.Betti
