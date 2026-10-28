import OAI.AlgebraicGeometry.Betti.ProjectivePresentationCohomology
import Mathlib.LinearAlgebra.Pi

/-! # Component Cohomology Extension -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ComponentCohomologyExtension

noncomputable section

/-! The original finite component Betti equivalence gives actual linear extension of a single component class. -/

open _root_.CategoryTheory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def componentCohomologyExtension (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents P.carrier) :
    (P.componentVariety C).rationalCohomology 2 →ₗ[ℚ] P.rationalCohomology 2 := by
  classical
  exact (P.componentBettiEquiv (ModuleCat.of ℚ ℚ) 2).symm.toLinearMap.comp
    (LinearMap.single ℚ (fun D => (P.componentVariety D).rationalCohomology 2) C)

theorem componentCohomologyExtension_components (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (C : irreducibleComponents P.carrier) (a : (P.componentVariety C).rationalCohomology 2) :
    P.componentBettiEquiv (ModuleCat.of ℚ ℚ) 2 (componentCohomologyExtension P C a) = Pi.single C a := by
  classical
  exact (P.componentBettiEquiv (ModuleCat.of ℚ ℚ) 2).apply_symm_apply _

theorem componentCohomologyExtension_sum (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [Fintype (irreducibleComponents P.carrier)] (a : P.rationalCohomology 2) :
    ∑ C, componentCohomologyExtension P C (P.componentBettiEquiv (ModuleCat.of ℚ ℚ) 2 a C) = a := by
  classical
  apply (P.componentBettiEquiv (ModuleCat.of ℚ ℚ) 2).injective
  rw [map_sum]
  simp only [componentCohomologyExtension_components]
  exact LinearMap.sum_single_apply _ _

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ComponentCohomologyExtension
