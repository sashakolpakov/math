import OAI.Analysis.PDE.Schauder.Calculus.Interior.MooreEquation
import OAI.Analysis.PDE.Schauder.Calculus.Interior.ThirdJet

noncomputable section
open Set
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Nonlinear OAI.Analysis.Normed.Function.Holder

local instance isoFirstGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance isoFirstSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance isoSecondGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance isoSecondSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance isoThirdGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance isoThirdSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem trilinear_norm_le_of_apply (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ v w z, ‖T v w z‖ ≤ C*‖v‖*‖w‖*‖z‖) : ‖T‖ ≤ C := by
  apply T.opNorm_le_bound hC
  intro v
  apply (T v).opNorm_le_bound (mul_nonneg hC (norm_nonneg _))
  intro w
  exact (T v w).opNorm_le_bound (by positivity) (h v w)

theorem trilinear_norm_le_isometric_pullback (e : E ≃ₗᵢ[ℝ] F)
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (U : F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ)
    (h : ∀ v w z, T v w z = U (e v) (e w) (e z)) : ‖T‖ ≤ ‖U‖ := by
  apply trilinear_norm_le_of_apply T (norm_nonneg _)
  intro v w z
  rw [h]
  calc
    _ ≤ ‖U (e v) (e w)‖*‖e z‖ := (U (e v) (e w)).le_opNorm (e z)
    _ ≤ (‖U (e v)‖*‖e w‖)*‖e z‖ :=
      mul_le_mul_of_nonneg_right ((U (e v)).le_opNorm (e w)) (norm_nonneg _)
    _ ≤ ((‖U‖*‖e v‖)*‖e w‖)*‖e z‖ := by
      gcongr
      exact U.le_opNorm (e v)
    _ = _ := by simp only [e.norm_map]

theorem trilinear_norm_eq_isometric_pullback (e : E ≃ₗᵢ[ℝ] F)
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (U : F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ)
    (h : ∀ v w z, T v w z = U (e v) (e w) (e z)) : ‖T‖ = ‖U‖ := by
  apply le_antisymm (trilinear_norm_le_isometric_pullback e T U h)
  apply trilinear_norm_le_isometric_pullback e.symm U T
  intro v w z
  simpa only [LinearIsometryEquiv.apply_symm_apply] using (h (e.symm v) (e.symm w) (e.symm z)).symm

theorem third_fderiv_isometry_comp (e : E ≃ₗᵢ[ℝ] F) (u : F → ℝ)
    (hu : ContDiff ℝ 3 u) (x v w z : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (u ∘ e))) x v w z =
      fderiv ℝ (fderiv ℝ (fderiv ℝ u)) (e x) (e v) (e w) (e z) := by
  rw [OAI.Analysis.PDE.Nonlinear.third_derivative_directional_hessian _ (hu.comp e.contDiff),
    directional_isometry_comp e u (hu.differentiable (by norm_num)) v]
  have hh := OAI.Analysis.PDE.Dirichlet.second_fderiv_comp_between _
    (OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (by norm_num) (e v))
    e.toContinuousLinearEquiv.toContinuousLinearMap x w z
  simpa only [OAI.Analysis.PDE.Nonlinear.third_derivative_directional_hessian u hu] using! hh

theorem norm_third_isometry_comp (e : E ≃ₗᵢ[ℝ] F) (u : F → ℝ)
    (hu : ContDiff ℝ 3 u) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (u ∘ e))) x‖ =
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) (e x)‖ :=
  trilinear_norm_eq_isometric_pullback e _ _ (third_fderiv_isometry_comp e u hu x)

theorem norm_third_sub_isometry_comp (e : E ≃ₗᵢ[ℝ] F) (u : F → ℝ)
    (hu : ContDiff ℝ 3 u) (x y : E) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (u ∘ e))) x-
      fderiv ℝ (fderiv ℝ (fderiv ℝ (u ∘ e))) y‖ =
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) (e x)-fderiv ℝ (fderiv ℝ (fderiv ℝ u)) (e y)‖ := by
  apply trilinear_norm_eq_isometric_pullback e
  intro v w z
  simp only [sub_apply,third_fderiv_isometry_comp e u hu]

end OAI.Analysis.PDE.Schauder
