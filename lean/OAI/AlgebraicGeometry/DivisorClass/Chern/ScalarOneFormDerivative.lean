import OAI.AlgebraicGeometry.DivisorClass.Chern.OneFormWedgeEvaluation
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Scalar One Form Derivative -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarOneFormDerivative

noncomputable section

/-! The actual exterior derivative of a scalar multiple of a one-form in coordinates. -/

open _root_.ContinuousAlternatingMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem extDeriv_one_apply (a : E → E [⋀^Fin 1]→L[ℝ] ℂ) (x : E) (v : Fin 2 → E) :
    extDeriv a x v = (fderiv ℝ a x (v 0)) (fun _ => v 1) -
      (fderiv ℝ a x (v 1)) (fun _ => v 0) := by
  have h0 : Fin.tail v = (fun _ : Fin 1 => v 1) := by funext i; fin_cases i; rfl
  have h1 : Fin.removeNth (1 : Fin 2) v = (fun _ : Fin 1 => v 0) := by funext i; fin_cases i; rfl
  simp [extDeriv, alternatizeUncurryFin_apply, Fin.sum_univ_two, h0, h1, sub_eq_add_neg]

theorem extDeriv_scalar_one (f : E → ℂ) (a : E → E [⋀^Fin 1]→L[ℝ] ℂ) (x : E)
    (hf : DifferentiableAt ℝ f x) (ha : DifferentiableAt ℝ a x) :
    extDeriv (fun y => f y • a y) x =
      AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (ofSubsingleton ℝ E ℂ (0 : Fin 1) (fderiv ℝ f x)) (a x) + f x • extDeriv a x := by
  ext v
  rw [extDeriv_one_apply, ContinuousAlternatingMap.add_apply, OneFormWedgeEvaluation.covectorWedge_one_one_apply,
    ContinuousAlternatingMap.smul_apply, extDeriv_one_apply]
  have hd := (hf.hasFDerivAt.smul ha.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => f y • a y) x = _ at hd
  rw [hd]
  simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  change (f x * fderiv ℝ a x (v 0) (fun _ => v 1) + (fderiv ℝ f x (v 0)) * a x (fun _ => v 1)) -
      (f x * fderiv ℝ a x (v 1) (fun _ => v 0) + (fderiv ℝ f x (v 1)) * a x (fun _ => v 0)) =
    (fderiv ℝ f x (v 0)) * a x (fun _ => v 1) - (fderiv ℝ f x (v 1)) * a x (fun _ => v 0) +
      f x * (fderiv ℝ a x (v 0) (fun _ => v 1) - fderiv ℝ a x (v 1) (fun _ => v 0))
  ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarOneFormDerivative
