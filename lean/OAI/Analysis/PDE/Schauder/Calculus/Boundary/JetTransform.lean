import OAI.Analysis.PDE.Nonlinear.Dilation
import OAI.Analysis.Normed.Function.Holder.Banach.Linear

/-! Actual lower jets and their Hölder norms under affine normalization. -/

noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def gradientPullbackCLM (L : E →L[ℝ] E) : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ E E ℝ).flip L

@[simp] theorem gradientPullbackCLM_apply (L : E →L[ℝ] E) (v : E →L[ℝ] ℝ) :
    gradientPullbackCLM L v = v.comp L := rfl

theorem norm_gradientPullbackCLM_le (L : E →L[ℝ] E) : ‖gradientPullbackCLM L‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  change ‖v.comp L‖ ≤ ‖L‖ * ‖v‖
  exact v.opNorm_comp_le L |>.trans_eq (mul_comm _ _)

def affineGradientHolder {α : ℝ} (hα : 0 ≤ α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap E (E →L[ℝ] ℝ) α) (x₀ : E) (L : E →L[ℝ] E) :
    OAI.Analysis.Normed.Function.Holder.HolderMap E (E →L[ℝ] ℝ) α :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (gradientPullbackCLM L) (holderLinearAffinePullback hα V x₀ L)

@[simp] theorem affineGradientHolder_value {α : ℝ} (hα : 0 ≤ α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap E (E →L[ℝ] ℝ) α) (x₀ : E) (L : E →L[ℝ] E) (x) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (affineGradientHolder hα V x₀ L) x =
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value V (x₀ + L x)).comp L := rfl

theorem norm_affineGradientHolder_le {α : ℝ} (hα : 0 ≤ α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap E (E →L[ℝ] ℝ) α) (x₀ : E) (L : E →L[ℝ] E) :
    ‖affineGradientHolder hα V x₀ L‖ ≤ ‖L‖ * (1 + ‖L‖^α) * ‖V‖ := by
  have hb := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_map_le (gradientPullbackCLM L) (holderLinearAffinePullback hα V x₀ L)
  change ‖OAI.Analysis.Normed.Function.Holder.HolderMap.map (gradientPullbackCLM L) (holderLinearAffinePullback hα V x₀ L)‖ ≤ _
  exact hb.trans ((mul_le_mul (norm_gradientPullbackCLM_le L)
    (OAI.Analysis.PDE.Nonlinear.norm_holderLinearAffinePullback_le hα V x₀ L) (norm_nonneg _) (norm_nonneg _)).trans_eq (by ring))

theorem affineGradientHolder_eq_fderiv {α : ℝ} (hα : 0 ≤ α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap E (E →L[ℝ] ℝ) α) (u : E → ℝ) (hu : Differentiable ℝ u)
    (x₀ : E) (L : E →L[ℝ] E) (x) (hV : OAI.Analysis.Normed.Function.Holder.HolderMap.value V (x₀ + L x) = fderiv ℝ u (x₀ + L x)) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (affineGradientHolder hα V x₀ L) x = fderiv ℝ (fun y => u (x₀ + L y)) x := by
  rw [affineGradientHolder_value, hV, OAI.Analysis.PDE.Nonlinear.fderiv_linearAffine u hu]

end OAI.Analysis.PDE.Schauder
