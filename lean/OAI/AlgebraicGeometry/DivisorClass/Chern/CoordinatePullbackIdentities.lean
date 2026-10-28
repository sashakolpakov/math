import OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.LinearPullbackLaws
import OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultOneFormCorrection

/-! # Coordinate Pullback Identities -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CoordinatePullbackIdentities

noncomputable section

/-! Coefficient values and restricted inverse identities for the original coordinate pullbacks. -/

open _root_.ContinuousAlternatingMap _root_.TopologicalSpace Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E F : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {U U' : Opens E} {V V' : Opens F} {n : ℕ}

theorem complexLinearOpenPullback_oneFormCoefficient (L : E →L[ℂ] F)
    (hL : MapsTo L (U : Set E) (V : Set F)) (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V 1) (x : U) (v : E) :
    AntiOneFormCoordinates.oneFormLinear (Complex.LinearOpenPullback.complexLinearOpenPullback L hL a x) v =
      AntiOneFormCoordinates.oneFormLinear (a ⟨L x, hL x.property⟩) (L v) := by
  rw [Complex.LinearOpenPullback.complexLinearOpenPullback_apply, AntiOneFormCoordinates.oneFormLinear_apply, AntiOneFormCoordinates.oneFormLinear_apply]
  rfl

theorem complexLinearOpenPullback_inverse_restrict (e : E ≃L[ℂ] F)
    (hi : MapsTo e.symm (V : Set F) (U : Set E))
    (h : MapsTo e (U' : Set E) (V' : Set F)) (hU : U' ≤ U) (hV : V' ≤ V)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n) :
    Complex.LinearOpenPullback.complexLinearOpenPullback e.toContinuousLinearMap h
      (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hV (Complex.LinearOpenPullback.complexLinearOpenPullback e.symm.toContinuousLinearMap hi a)) =
        Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hU a := by
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  rw [Complex.LinearOpenPullback.complexLinearOpenPullback_apply, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict_apply,
    Complex.LinearOpenPullback.complexLinearOpenPullback_apply]
  ext v
  change a ⟨e.symm (e x), hi (hV (h x.property))⟩ (fun i => e.symm (e (v i))) = a ⟨x, hU x.property⟩ v
  simp only [e.symm_apply_apply]

theorem complexLinearOpenPullback_closed (L : E →L[ℂ] F)
    (hL : MapsTo L (U : Set E) (V : Set F)) (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V n)
    (ha : DolbeaultOpen.openDolbeaultD n a = 0) : DolbeaultOpen.openDolbeaultD n (Complex.LinearOpenPullback.complexLinearOpenPullback L hL a) = 0 := by
  rw [Complex.LinearOpenPullback.openDolbeaultD_complexLinearPullback, ha]
  exact (Complex.LinearOpenPullback.complexLinearOpenPullback L hL).map_zero

theorem correctDolbeaultOneForm_add_dbar (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 1) {g : E → ℂ}
    (hg : ContDiffOn ℝ ∞ g (U : Set E)) :
    DolbeaultOneFormCorrection.correctDolbeaultOneForm a g hg + DolbeaultOpen.openDolbeaultD 0 (ScalarDolbeaultCommutation.scalarOpenZeroForm U g hg) = a := by
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  apply ContinuousAlternatingMap.ext
  intro v
  change (a x v - DolbeaultOpen.openDolbeaultD 0 (ScalarDolbeaultCommutation.scalarOpenZeroForm U g hg) x v) +
    DolbeaultOpen.openDolbeaultD 0 (ScalarDolbeaultCommutation.scalarOpenZeroForm U g hg) x v = a x v
  ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CoordinatePullbackIdentities
