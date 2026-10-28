import OAI.AlgebraicTopology.Kunneth.ProjectiveFinitenessLe
import OAI.AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange
import OAI.AlgebraicTopology.DeRham.Comparison.Projective
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicPrimitive

/-! # Forms Finite -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.FormsFinite

noncomputable section

open _root_.CategoryTheory

/-- Ordinary complex cohomology of the actual analytic realization is
finite-dimensional, by rational finiteness and coefficient extension. -/
theorem projective_complexCohomology_finite (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    FiniteDimensional ℂ (V.complexCohomology n) := by
  let _ : FiniteDimensional ℚ (V.rationalCohomology n) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite V n
  let e := ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexificationEquiv (Betti.Scheme.schemePointSpace V.toOver) n
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

/-- Actual de Rham cohomology inherits this finiteness through the proved
integration comparison. -/
theorem projective_deRhamCohomology_finite (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    FiniteDimensional ℂ (V.deRhamCohomology n) := by
  let _ := projective_complexCohomology_finite V n
  exact Module.Finite.of_injective (V.deRhamBettiIso n).toLinearEquiv.toLinearMap
    (V.deRhamBettiIso n).toLinearEquiv.injective

/-- The space of closed holomorphic one-forms is finite-dimensional because
its genuine class map is injective on a compact complex manifold. -/
theorem projective_closedHolomorphicOneForms_finite (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    FiniteDimensional ℂ
      (AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms V.analyticModel V.analyticSpace 1 0) := by
  let _ := projective_deRhamCohomology_finite V 1
  exact Module.Finite.of_injective
    (AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.manifoldPureFormClass V.analyticModel V.analyticSpace 1 0)
    ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction.holomorphic_formClass_injective

end

end OAI.AlgebraicGeometry.Albanese.Construction.FormsFinite
