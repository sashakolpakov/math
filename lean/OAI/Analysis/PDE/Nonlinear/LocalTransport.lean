import OAI.Analysis.PDE.Nonlinear.LocalLinear
import OAI.Analysis.PDE.Dirichlet.MatrixTransport
import OAI.Analysis.Normed.Function.Holder.C2HolderIsometry

/-! Local Hölder jets and the linear bootstrap are invariant under coordinate isometries. -/

noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet

theorem HasLocalHolderBound.congr {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {α : ℝ} {f g : E → F} {x₀ : E}
    (hf : HasLocalHolderBound α f x₀) (hfg : f =ᶠ[𝓝 x₀] g) :
    HasLocalHolderBound α g x₀ := by
  obtain ⟨r, hr, C, hC, hh⟩ := hf
  obtain ⟨s, hs, he⟩ := Metric.eventually_nhds_iff.mp hfg
  refine ⟨min r s, lt_min hr hs, C, hC, ?_⟩
  intro x hx y hy
  have hx' := mem_ball.mp hx
  have hy' := mem_ball.mp hy
  rw [← he (lt_of_lt_of_le hx' (min_le_right _ _)),
    ← he (lt_of_lt_of_le hy' (min_le_right _ _))]
  exact hh x (lt_of_lt_of_le hx' (min_le_left _ _)) y
    (lt_of_lt_of_le hy' (min_le_left _ _))

theorem HasLocalHolderBound.comp_isometry {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    {α : ℝ} {f : F → G} (L : E ≃ₗᵢ[ℝ] F) (x₀ : E)
    (hf : HasLocalHolderBound α f (L x₀)) :
    HasLocalHolderBound α (f ∘ L) x₀ := by
  obtain ⟨r, hr, C, hC, hh⟩ := hf
  refine ⟨r, hr, C, hC, ?_⟩
  intro x hx y hy
  have h := hh (L x) (by simpa only [mem_ball, L.dist_map] using hx)
    (L y) (by simpa only [mem_ball, L.dist_map] using hy)
  simpa only [Function.comp_apply, ← dist_eq_norm, L.dist_map] using h

theorem HasLocalHolderBound.map_clm {E F G : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {α : ℝ} {f : E → F} {x₀ : E} (hf : HasLocalHolderBound α f x₀)
    (L : F →L[ℝ] G) : HasLocalHolderBound α (L ∘ f) x₀ := by
  obtain ⟨r, hr, C, hC, hh⟩ := hf
  refine ⟨r, hr, (‖L‖ + 1) * C, mul_pos (by positivity) hC, ?_⟩
  intro x hx y hy
  change ‖L (f x) - L (f y)‖ ≤ _
  rw [← map_sub]
  calc
    ‖L (f x - f y)‖ ≤ ‖L‖ * ‖f x - f y‖ := L.le_opNorm _
    _ ≤ ‖L‖ * (C * ‖x - y‖ ^ α) := mul_le_mul_of_nonneg_left (hh x hx y hy) (norm_nonneg _)
    _ ≤ (‖L‖ + 1) * C * ‖x - y‖ ^ α := by
      have : 0 ≤ C * ‖x - y‖ ^ α := mul_nonneg hC.le (Real.rpow_nonneg (norm_nonneg _) _)
      nlinarith

theorem localHolderBound_fderiv_linear_composition {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {α : ℝ} (L : E ≃ₗᵢ[ℝ] F) (P : G →L[ℝ] H) (f : F → G)
    (hf : ContDiff ℝ 1 f) (x₀ : E)
    (hDf : HasLocalHolderBound α (fderiv ℝ f) (L x₀)) :
    HasLocalHolderBound α (fderiv ℝ (P ∘ f ∘ L)) x₀ := by
  let J : (F →L[ℝ] G) →L[ℝ] (E →L[ℝ] H) :=
    (ContinuousLinearMap.compL ℝ E G H P).comp
      ((ContinuousLinearMap.compL ℝ E F G).flip L.toContinuousLinearEquiv.toContinuousLinearMap)
  apply ((hDf.comp_isometry L x₀).map_clm J).congr
  filter_upwards [] with x
  change P.comp ((fderiv ℝ f (L x)).comp L.toContinuousLinearEquiv.toContinuousLinearMap) = _
  exact ((P.hasFDerivAt.comp x ((hf.differentiable one_ne_zero (L x)).hasFDerivAt.comp x
    L.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt)).fderiv).symm

end OAI.Analysis.PDE.Nonlinear
