import OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultOpen

/-! # Linear Dolbeault Pullback -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.LinearDolbeaultPullback

noncomputable section

/-! The actual local Dolbeault operator commutes with pullback by a complex-linear map. -/

open _root_.ContinuousAlternatingMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] {n : ℕ}

def rawComplexLinearPullback (L : E →L[ℂ] F) (a : Analysis.DifferentialForms.Manifold.Basic.RawForm F n) (x : E) : Analysis.DifferentialForms.Manifold.Basic.FormValue E n :=
  (a (L x)).compContinuousLinearMap (L.restrictScalars ℝ)

theorem rawComplexLinearPullback_fderiv_apply (L : E →L[ℂ] F) {a : Analysis.DifferentialForms.Manifold.Basic.RawForm F n} {x : E}
    (ha : DifferentiableAt ℝ a (L x)) (v : E) :
    fderiv ℝ (rawComplexLinearPullback L a) x v =
      (fderiv ℝ a (L x) (L v)).compContinuousLinearMap (L.restrictScalars ℝ) := by
  let C : Analysis.DifferentialForms.Manifold.Basic.FormValue F n →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n := compContinuousLinearMapCLM (L.restrictScalars ℝ)
  have hd := (C.hasFDerivAt.comp x (ha.hasFDerivAt.comp x (L.restrictScalars ℝ).hasFDerivAt)).fderiv
  exact congrArg (fun D : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n => D v) hd

theorem rawComplexLinearPullback_antilinearPart (L : E →L[ℂ] F) {a : Analysis.DifferentialForms.Manifold.Basic.RawForm F n} {x : E}
    (ha : DifferentiableAt ℝ a (L x)) (v : E) :
    Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (fderiv ℝ (rawComplexLinearPullback L a) x) v =
      (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM F (Analysis.DifferentialForms.Manifold.Basic.FormValue F n) (fderiv ℝ a (L x)) (L v)).compContinuousLinearMap
        (L.restrictScalars ℝ) := by
  rw [Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply, rawComplexLinearPullback_fderiv_apply L ha,
    rawComplexLinearPullback_fderiv_apply L ha, L.map_smul]
  ext w
  rfl

theorem extDerivDoublePrime_complexLinearPullback (L : E →L[ℂ] F) {a : Analysis.DifferentialForms.Manifold.Basic.RawForm F n} {x : E}
    (ha : DifferentiableAt ℝ a (L x)) :
    Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime (rawComplexLinearPullback L a) x =
      (Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime a (L x)).compContinuousLinearMap (L.restrictScalars ℝ) := by
  ext v
  simp only [Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime, alternatizeUncurryFin_apply, compContinuousLinearMap_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [rawComplexLinearPullback_antilinearPart L ha]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.LinearDolbeaultPullback
