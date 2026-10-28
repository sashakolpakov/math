import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Affine
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.AffineHolder
import OAI.Analysis.PDE.Nonlinear.Average

/-! Uniform lower-jet Hölder bounds under a fixed localization dilation. -/

noncomputable section
open Set Metric Filter
open scoped Topology
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder

theorem norm_holderAffinePullback_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} (hα : 0 ≤ α) (f : OAI.Analysis.Normed.Function.Holder.HolderMap E F α) (x₀ : E) (r : ℝ) :
    ‖OAI.Analysis.PDE.Schauder.holderAffinePullback hα f x₀ r‖ ≤ (1 + |r| ^ α) * ‖f‖ := by
  apply OAI.Analysis.Normed.Function.Holder.HolderMap.norm_le_of_bounds hα (by positivity)
  · intro x
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le f (x₀ + r • x)).trans (by
      nlinarith only [norm_nonneg f, mul_nonneg (Real.rpow_nonneg (abs_nonneg r) α) (norm_nonneg f)])
  · intro x y
    have he : x₀ + r • x - (x₀ + r • y) = r • (x - y) := by rw [smul_sub]; abel
    have hh := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le f (x₀ + r • x) (x₀ + r • y)
    rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs,
      Real.mul_rpow (abs_nonneg r) (norm_nonneg _)] at hh
    change ‖OAI.Analysis.Normed.Function.Holder.HolderMap.value f (x₀ + r • x) - OAI.Analysis.Normed.Function.Holder.HolderMap.value f (x₀ + r • y)‖ ≤ _
    rw [dist_eq_norm]
    apply hh.trans
    nlinarith only [mul_nonneg (norm_nonneg f) (Real.rpow_nonneg (norm_nonneg (x - y)) α)]

theorem fderiv_dilation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E → ℝ) (hu : Differentiable ℝ u) (x₀ x : E) (r : ℝ) :
    fderiv ℝ (fun y => u (x₀ + r • y)) x = r • fderiv ℝ u (x₀ + r • x) := by
  have hd : HasFDerivAt (fun y : E => x₀ + r • y) (r • ContinuousLinearMap.id ℝ E) x := by
    simpa only [zero_add, Pi.smul_apply, id_eq] using ((hasFDerivAt_id x).const_smul r).const_add x₀
  have hh := ((hu _).hasFDerivAt.comp x hd).fderiv
  simp only [Function.comp_def] at hh
  rw [hh]
  apply ContinuousLinearMap.ext
  intro y
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply, map_smul]

theorem norm_holderLinearAffinePullback_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} (hα : 0 ≤ α) (f : OAI.Analysis.Normed.Function.Holder.HolderMap E F α) (x₀ : E) (L : E →L[ℝ] E) :
    ‖OAI.Analysis.PDE.Schauder.holderLinearAffinePullback hα f x₀ L‖ ≤ (1 + ‖L‖ ^ α) * ‖f‖ := by
  apply OAI.Analysis.Normed.Function.Holder.HolderMap.norm_le_of_bounds hα (by positivity)
  · intro x
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le f (x₀ + L x)).trans (by
      nlinarith only [norm_nonneg f, mul_nonneg (Real.rpow_nonneg (norm_nonneg L) α) (norm_nonneg f)])
  · intro x y
    have he : x₀ + L x - (x₀ + L y) = L (x - y) := by rw [map_sub]; abel
    have hh := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le f (x₀ + L x) (x₀ + L y)
    rw [dist_eq_norm, he] at hh
    have hb := Real.rpow_le_rpow (norm_nonneg _) (L.le_opNorm (x - y)) hα
    rw [Real.mul_rpow (norm_nonneg L) (norm_nonneg (x - y))] at hb
    change ‖OAI.Analysis.Normed.Function.Holder.HolderMap.value f (x₀ + L x) - OAI.Analysis.Normed.Function.Holder.HolderMap.value f (x₀ + L y)‖ ≤ _
    rw [dist_eq_norm]
    apply hh.trans
    apply (mul_le_mul_of_nonneg_left hb (norm_nonneg f)).trans
    nlinarith only [mul_nonneg (norm_nonneg f) (Real.rpow_nonneg (norm_nonneg (x - y)) α)]

theorem fderiv_linearAffine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E → ℝ) (hu : Differentiable ℝ u) (x₀ x : E) (L : E →L[ℝ] E) :
    fderiv ℝ (fun y => u (x₀ + L y)) x = (fderiv ℝ u (x₀ + L x)).comp L := by
  have hd : HasFDerivAt (fun y : E => x₀ + L y) L x := by
    simpa only [zero_add] using (L.hasFDerivAt (x := x)).const_add x₀
  simpa only [Function.comp_def] using ((hu _).hasFDerivAt.comp x hd).fderiv

theorem contDiffAt_of_linearAffine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : E → ℝ) (x₀ : E) (L : E ≃L[ℝ] E)
    (hc : ContDiffAt ℝ 2 (fun y => w (x₀ + L y)) 0) : ContDiffAt ℝ 2 w x₀ := by
  let ψ := fun x : E => L.symm (x - x₀)
  have hψ : ContDiff ℝ 2 ψ := L.symm.contDiff.comp (contDiff_id.sub contDiff_const)
  have hψzero : ψ x₀ = 0 := by simp only [ψ, sub_self, map_zero]
  have hc' : ContDiffAt ℝ 2 (fun y => w (x₀ + L y)) (ψ x₀) := by
    rw [hψzero]
    exact hc
  have hh := hc'.comp x₀ hψ.contDiffAt
  have he : (fun x => w (x₀ + L (ψ x))) = w := by
    funext x
    simp only [ψ, L.apply_symm_apply, add_sub_cancel]
  simpa only [Function.comp_def, he] using hh

theorem contDiffAt_of_dilated_cutoff {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w : E → ℝ) (x₀ : E) {r : ℝ} (hr : 0 < r)
    (hc : ContDiff ℝ 2 (fun y => OAI.Analysis.PDE.Schauder.radialCutoff (1 / 4) y * w (x₀ + r • y))) :
    ContDiffAt ℝ 2 w x₀ := by
  let ψ := fun x : E => r⁻¹ • (x - x₀)
  have hψ : ContDiff ℝ 2 ψ := (contDiff_id.sub contDiff_const).const_smul _
  have hψzero : ψ x₀ = 0 := by simp only [ψ, sub_self, smul_zero]
  have he : (fun y => OAI.Analysis.PDE.Schauder.radialCutoff (1 / 4) (ψ y) * w (x₀ + r • ψ y)) =ᶠ[𝓝 x₀] w := by
    have hn : ∀ᶠ y in 𝓝 x₀, ψ y ∈ ball 0 (1 / 4) :=
      (hψ.continuous.tendsto x₀).eventually (by rw [hψzero]; exact ball_mem_nhds 0 (by norm_num))
    filter_upwards [hn] with y hy
    have hnorm : ‖ψ y‖ ≤ 1 / 4 := by
      exact le_of_lt (by simpa only [mem_ball, dist_zero_right] using hy)
    rw [OAI.Analysis.PDE.Schauder.radialCutoff_one (by norm_num) hnorm, one_mul]
    have hid : x₀ + r • ψ y = y := by
      simp only [ψ, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      abel
    rw [hid]
  exact ((hc.comp hψ).contDiffAt).congr_of_eventuallyEq he.symm

end OAI.Analysis.PDE.Nonlinear
