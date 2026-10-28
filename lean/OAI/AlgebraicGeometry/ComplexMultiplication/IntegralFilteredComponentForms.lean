import OAI.AlgebraicGeometry.ComplexMultiplication.ManifoldFiltrationPullback
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.ProjectiveFilteredComponents
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveNaturality

/-! # Integral Filtered Component Forms -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.IntegralFilteredComponentForms

noncomputable section

/-! # Actual restriction of filtered forms to the genuine integral components -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local notation "P" => V.presentation

/-- Restrict the same actual closed form along each original component inclusion. -/
def integralFilteredComponentForm (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace n) :
    (P).componentClosedForms n :=
  ((P).componentClosedFormsEquiv n).symm fun C =>
    Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map ((P).componentInclusionOver C))
      (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.real_contMDiff_map ((P).componentInclusionOver C) ∞) n form

/-- The restricted family lies in the same actual Hodge filtration. -/
theorem integralFilteredComponentForm_filtered (n : ℕ) (r : ℤ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace n)
    (hf : form.val ∈ Comparison.Betti.ManifoldFormFiltration.Hodge.manifoldFormFiltration V.analyticModel V.analyticSpace n r) :
    (integralFilteredComponentForm V n form).val ∈ Analysis.HodgeTheory.Decomposition.Core.Constructions.filteredForms (P) n r := by
  rw [Comparison.Betti.Projective.ProjectiveFilteredComponents.Hodge.mem_projectiveFilteredForms_iff_components]
  intro C
  change (Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map ((P).componentInclusionOver C))
    (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.real_contMDiff_map ((P).componentInclusionOver C) ∞) n form).val ∈ _
  exact ManifoldFiltrationPullback.manifoldFormFiltration_pullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map ((P).componentInclusionOver C))
    (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complex_contMDiff_map ((P).componentInclusionOver C) ∞) n r form.val hf

set_option backward.isDefEq.respectTransparency false in
/-- The canonical class of the restricted family is precisely the original whole-variety class. -/
theorem integralFilteredComponentForm_class (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace n) :
    (P).closedFormBettiClass n (integralFilteredComponentForm V n form) =
      (V.deRhamBettiIso n).hom (V.deRhamClass n form) := by
  apply ((P).componentBettiEquiv (ModuleCat.of ℂ ℂ) n).injective
  funext C
  rw [(P).componentBettiEquiv_closedFormBettiClass,
    (P).componentBettiEquiv_apply]
  have hc : (P).componentClosedFormsEquiv n (integralFilteredComponentForm V n form) C =
      Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map ((P).componentInclusionOver C))
        (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.real_contMDiff_map ((P).componentInclusionOver C) ∞) n form := by
    exact congrFun (((P).componentClosedFormsEquiv n).apply_symm_apply _) C
  rw [hc]
  have hp := Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldDeRhamFormClass_pullback_apply
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map ((P).componentInclusionOver C))
    (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.real_contMDiff_map ((P).componentInclusionOver C) ∞) n form
  have hn := ConcreteCategory.congr_hom
    (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamBettiIso_naturality ((P).componentInclusionOver C) n)
      (V.deRhamClass n form)
  simp only [ModuleCat.comp_apply] at hn
  exact (congrArg (((P).componentVariety C).deRhamBettiIso n).hom hp).symm.trans hn.symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.IntegralFilteredComponentForms
