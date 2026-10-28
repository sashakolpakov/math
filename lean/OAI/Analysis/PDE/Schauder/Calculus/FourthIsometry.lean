import OAI.Analysis.PDE.Schauder.Calculus.ThirdIsometry
import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.Tensor

noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Elliptic

local instance fourthIso1Group (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fourthIso1Space (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fourthIso2Group (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthIso2Space (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthIso3Group (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthIso3Space (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthIso4Group (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthIso4Space (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem quadrilinear_norm_le_of_apply
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ q v w z, ‖T q v w z‖ ≤ C*‖q‖*‖v‖*‖w‖*‖z‖) : ‖T‖ ≤ C := by
  apply T.opNorm_le_bound hC
  intro q
  exact trilinear_norm_le_of_apply (T q) (mul_nonneg hC (norm_nonneg q)) (h q)

theorem quadrilinear_norm_le_isometric_pullback (e : E ≃ₗᵢ[ℝ] F)
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (U : F →L[ℝ] F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ)
    (h : ∀ q v w z, T q v w z = U (e q) (e v) (e w) (e z)) : ‖T‖ ≤ ‖U‖ := by
  apply T.opNorm_le_bound (norm_nonneg U)
  intro q
  calc
    ‖T q‖ ≤ ‖U (e q)‖ := trilinear_norm_le_isometric_pullback e (T q) (U (e q)) (h q)
    _ ≤ ‖U‖*‖e q‖ := U.le_opNorm (e q)
    _ = ‖U‖*‖q‖ := by rw [e.norm_map]

theorem quadrilinear_norm_eq_isometric_pullback (e : E ≃ₗᵢ[ℝ] F)
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (U : F →L[ℝ] F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ)
    (h : ∀ q v w z, T q v w z = U (e q) (e v) (e w) (e z)) : ‖T‖ = ‖U‖ := by
  apply le_antisymm (quadrilinear_norm_le_isometric_pullback e T U h)
  apply quadrilinear_norm_le_isometric_pullback e.symm U T
  intro q v w z
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    (h (e.symm q) (e.symm v) (e.symm w) (e.symm z)).symm

theorem fourth_fderiv_isometry_comp (e : E ≃ₗᵢ[ℝ] F) (u : F → ℝ)
    (hu : ContDiff ℝ 4 u) (x q v w z : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (u ∘ e)))) x q v w z =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) (e x) (e q) (e v) (e w) (e z) := by
  rw [OAI.Analysis.PDE.Elliptic.fourth_derivative_directional_third _ (hu.comp e.contDiff),
    directional_isometry_comp e u (hu.differentiable (by norm_num)) q]
  rw [third_fderiv_isometry_comp e _ (OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (by norm_num) (e q))]
  rw [OAI.Analysis.PDE.Elliptic.fourth_derivative_directional_third u hu]

theorem norm_fourth_isometry_comp (e : E ≃ₗᵢ[ℝ] F) (u : F → ℝ)
    (hu : ContDiff ℝ 4 u) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (u ∘ e)))) x‖ =
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) (e x)‖ :=
  quadrilinear_norm_eq_isometric_pullback e _ _ (fourth_fderiv_isometry_comp e u hu x)

theorem norm_fourth_sub_isometry_comp (e : E ≃ₗᵢ[ℝ] F) (u : F → ℝ)
    (hu : ContDiff ℝ 4 u) (x y : E) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (u ∘ e)))) x-
      fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (u ∘ e)))) y‖ =
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) (e x)-
        fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) (e y)‖ := by
  apply quadrilinear_norm_eq_isometric_pullback e
  intro q v w z
  simp only [sub_apply,fourth_fderiv_isometry_comp e u hu]

end OAI.Analysis.PDE.Schauder
