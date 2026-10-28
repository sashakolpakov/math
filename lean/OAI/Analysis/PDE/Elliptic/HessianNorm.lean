import OAI.Analysis.PDE.Elliptic.HessianTrace

open InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem toDual_fderiv_gradient {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x v : E) :
    toDual ℝ E (fderiv ℝ (gradient f) x v) = fderiv ℝ (fderiv ℝ f) x v := by
  ext w
  exact inner_fderiv_gradient hf x v w

theorem norm_fderiv_gradient {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    ‖fderiv ℝ (gradient f) x‖ = ‖fderiv ℝ (fderiv ℝ f) x‖ := by
  apply ContinuousLinearMap.opNorm_ext
  intro v
  rw [← toDual_fderiv_gradient hf x v]
  exact ((toDual ℝ E).norm_map _).symm

theorem norm_fderiv_gradient_sub {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x y : E) :
    ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ =
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ := by
  apply ContinuousLinearMap.opNorm_ext
  intro v
  simp only [sub_apply]
  rw [← toDual_fderiv_gradient hf x v, ← toDual_fderiv_gradient hf y v, ← map_sub]
  exact ((toDual ℝ E).norm_map _).symm

end OAI.Analysis.PDE.Elliptic
