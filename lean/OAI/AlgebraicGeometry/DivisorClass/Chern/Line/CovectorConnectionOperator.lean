import OAI.AlgebraicGeometry.DivisorClass.Chern.OperatorConnectionCurvature
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ConnectionSymbols
import Mathlib.Topology.Order.Compact

/-! # Covector Connection Operator -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.CovectorConnectionOperator

noncomputable section

section

/-! The original line covector derivative as a genuine operator-valued connection. -/

open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance lineOperator_formNormed (n : ℕ) : NormedAddCommGroup (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) := inferInstance
local instance lineOperator_formSpace (n : ℕ) : NormedSpace ℝ (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) := inferInstance
local instance lineOperator_endNormed (n : ℕ) : NormedAddCommGroup (Analysis.DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) := inferInstance
local instance lineOperator_endSpace (n : ℕ) : NormedSpace ℝ (Analysis.DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) := inferInstance
local instance lineOperator_directionNormed (n : ℕ) : NormedAddCommGroup (E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) := inferInstance
local instance lineOperator_directionSpace (n : ℕ) : NormedSpace ℝ (E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) := inferInstance

def covectorActionOperator (n : ℕ) : (E →L[ℝ] E) →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n :=
  (ContinuousAlternatingMap.fderivCompContinuousLinearMapCLM ℂ
    (ContinuousLinearMap.id ℝ E)).flip

theorem covectorActionOperator_apply (n : ℕ) (G : E →L[ℝ] E) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    covectorActionOperator n G a = Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction n G a := rfl

def lineCovectorConnectionOperator (n : ℕ) (G : E →L[ℝ] E →L[ℝ] E)
    (A : E →L[ℝ] ℂ) : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n :=
  -((covectorActionOperator n).comp G) + (ContinuousLinearMap.lsmul ℝ ℂ).comp A

theorem lineCovectorConnectionOperator_apply (n : ℕ) (G : E →L[ℝ] E →L[ℝ] E)
    (A : E →L[ℝ] ℂ) (v : E) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    lineCovectorConnectionOperator n G A v a =
      -Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction n (G v) a + A v • a := rfl

theorem lineCovectorConnectionDerivative_operator (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x v : E) :
    ConnectionSymbols.lineCovectorConnectionDerivative n G A a x v =
      OperatorConnectionCurvature.operatorConnectionDerivative (fun y => lineCovectorConnectionOperator n (G y) (A y)) a x v := by
  rw [ConnectionSymbols.lineCovectorConnectionDerivative_apply, Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorConnectionDerivative_apply,
    OperatorConnectionCurvature.operatorConnectionDerivative, lineCovectorConnectionOperator_apply]
  abel

theorem lineCovectorConnectionOperator_differentiableAt (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) {x : E}
    (hG : DifferentiableAt ℝ G x) (hA : DifferentiableAt ℝ A x) :
    DifferentiableAt ℝ (fun y => lineCovectorConnectionOperator n (G y) (A y)) x :=
  ((differentiableAt_const (covectorActionOperator n)).clm_comp hG).neg.add
    ((differentiableAt_const (ContinuousLinearMap.lsmul ℝ ℂ)).clm_comp hA)

theorem lineCovectorConnectionOperator_derivative (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) {x : E}
    (hG : DifferentiableAt ℝ G x) (hA : DifferentiableAt ℝ A x) (v w : E) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    fderiv ℝ (fun y => lineCovectorConnectionOperator n (G y) (A y)) x v w a =
      -Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction n (fderiv ℝ G x v w) a + fderiv ℝ A x v w • a := by
  have hL := (hasFDerivAt_const (covectorActionOperator (E := E) n) x).clm_comp hG.hasFDerivAt
  have hS := (hasFDerivAt_const
    (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) x).clm_comp hA.hasFDerivAt
  have hd := congrArg (fun T => T v w a) (hL.neg.add hS).fderiv
  simp only [_root_.add_apply, _root_.neg_apply, ContinuousLinearMap.comp_apply,
    _root_.zero_apply, map_zero, add_zero] at hd
  exact hd

end

/-! Ordinary first derivatives are controlled by the original covariant derivative and a bounded zeroth-order connection term. -/

open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] lineOperator_formNormed lineOperator_formSpace
  lineOperator_endNormed lineOperator_endSpace lineOperator_directionNormed lineOperator_directionSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lineCovectorConnectionOperator_smoothOn (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) {U : Set E}
    (hG : ContDiffOn ℝ ∞ G U) (hA : ContDiffOn ℝ ∞ A U) :
    ContDiffOn ℝ ∞ (fun x => lineCovectorConnectionOperator n (G x) (A x)) U :=
  ((contDiffOn_const (c := covectorActionOperator n)).clm_comp hG).neg.add
    ((contDiffOn_const (c := (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n))).clm_comp hA)

theorem lineCovectorConnectionOperator_bound (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) {U T : Set E}
    (hG : ContDiffOn ℝ ∞ G U) (hA : ContDiffOn ℝ ∞ A U) (hT : IsCompact T) (hTU : T ⊆ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ T, ‖lineCovectorConnectionOperator n (G x) (A x)‖ ≤ C := by
  obtain ⟨B, hb⟩ := hT.bddAbove_image
    ((lineCovectorConnectionOperator_smoothOn n G A hG hA).continuousOn.mono hTU).norm
  exact ⟨max B 0 + 1, by positivity, fun x hx =>
    (hb ⟨x, hx, rfl⟩).trans ((le_max_left B 0).trans (by linarith))⟩

theorem lineCovectorDerivative_direction_norm (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x v : E) :
    ‖fderiv ℝ a x v‖ ≤ ‖ConnectionSymbols.lineCovectorConnectionDerivative n G A a x‖ * ‖v‖ +
      ‖lineCovectorConnectionOperator n (G x) (A x)‖ * ‖v‖ * ‖a x‖ := by
  have heq : fderiv ℝ a x v = ConnectionSymbols.lineCovectorConnectionDerivative n G A a x v -
      lineCovectorConnectionOperator n (G x) (A x) v (a x) := by
    rw [lineCovectorConnectionDerivative_operator, OperatorConnectionCurvature.operatorConnectionDerivative]
    abel
  rw [heq]
  exact (norm_sub_le _ _).trans (add_le_add
    ((ConnectionSymbols.lineCovectorConnectionDerivative n G A a x).le_opNorm v)
    (((lineCovectorConnectionOperator n (G x) (A x) v).le_opNorm (a x)).trans
      (mul_le_mul_of_nonneg_right ((lineCovectorConnectionOperator n (G x) (A x)).le_opNorm v) (norm_nonneg _))))

theorem lineCovectorDerivative_unit_sq (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x v : E)
    (hv : ‖v‖ = 1) {C : ℝ} (hC : 0 ≤ C) (hb : ‖lineCovectorConnectionOperator n (G x) (A x)‖ ≤ C) :
    ‖fderiv ℝ a x v‖ ^ 2 ≤ 2 * ‖ConnectionSymbols.lineCovectorConnectionDerivative n G A a x‖ ^ 2 + 2 * C ^ 2 * ‖a x‖ ^ 2 := by
  have hn := lineCovectorDerivative_direction_norm n G A a x v
  rw [hv, mul_one, mul_one] at hn
  have hh := hn.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hb (norm_nonneg _)))
  have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (mul_nonneg hC (norm_nonneg _)))).mpr hh
  nlinarith only [hs, sq_nonneg (‖ConnectionSymbols.lineCovectorConnectionDerivative n G A a x‖ - C * ‖a x‖)]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.CovectorConnectionOperator
