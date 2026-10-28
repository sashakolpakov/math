import OAI.Analysis.PDE.Schauder.Calculus.Schauder.CutoffForcing
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Cutoff

/-! Local C² to C²,α bootstrap for small Hölder perturbations, with the exponent unchanged. -/

noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem cutoff_small_coefficient_holder {m : ℕ} (hm : 3 ≤ m) {α R : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (B : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (hB : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = 0)
    (hsmall : 2 * ((m : ℝ) * m * ‖B‖) * ‖poissonHolderOperator hm hα hα1 R‖ < 1)
    (hPD : ∀ x, (1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B x).PosDef)
    (F : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (χ u : EuclideanSpace ℝ (Fin m) → ℝ)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hχR : tsupport χ ⊆ closedBall 0 R) (hu : ContDiff ℝ 2 u)
    (heq : ∀ x ∈ Function.support χ,
      nondivergenceOperator (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y) u x = OAI.Analysis.Normed.Function.Holder.HolderMap.value F x) :
    ∃ U : GlobalC2Holder m α, globalC2Value U = fun x => χ x * u x := by
  let A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α :=
    OAI.Analysis.Normed.Function.Holder.HolderMap.constant 1 - B
  have hA (x) : OAI.Analysis.Normed.Function.Holder.HolderMap.value A x = 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B x := rfl
  let f : SupportedHolder m α R :=
    ⟨cutoffForcing hα.le hα1.le A F χ u hχ hχc hu, by
      intro x hx
      exact cutoffForcing_zero hα.le hα1.le A F χ u hχ hχc hu x (fun h => hx (hχR h))⟩
  obtain ⟨U, hU, hbound⟩ := compact_C2_small_coefficient_holder hm hα hα1 B hB hsmall hPD
    (fun x => χ x * u x) ((hχ.of_le (by norm_num)).mul hu) hχc.mul_right f (by
      intro x
      change nondivergenceOperator (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y) (fun y => χ y * u y) x =
        OAI.Analysis.Normed.Function.Holder.HolderMap.value (cutoffForcing hα.le hα1.le A F χ u hχ hχc hu) x
      exact cutoffForcing_equation hα.le hα1.le A F χ u hχ hχc hu heq x)
  exact ⟨U, hU⟩

theorem local_small_coefficient_holder {m : ℕ} (hm : 3 ≤ m) {α R : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (B : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (hB : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = 0)
    (hsmall : 2 * ((m : ℝ) * m * ‖B‖) * ‖poissonHolderOperator hm hα hα1 R‖ < 1)
    (hPD : ∀ x, (1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B x).PosDef)
    (F : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (χ u : EuclideanSpace ℝ (Fin m) → ℝ)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hχR : tsupport χ ⊆ closedBall 0 R) (hu : ContDiff ℝ 2 u)
    (heq : ∀ x ∈ Function.support χ,
      nondivergenceOperator (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y) u x = OAI.Analysis.Normed.Function.Holder.HolderMap.value F x)
    (Ω : Set (EuclideanSpace ℝ (Fin m))) (hΩ : IsOpen Ω) (hχone : ∀ x ∈ Ω, χ x = 1) :
    ∃ C > 0, ∀ x ∈ Ω, ∀ y ∈ Ω,
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ C * ‖x - y‖ ^ α := by
  obtain ⟨U, hU⟩ := cutoff_small_coefficient_holder hm hα hα1 B hB hsmall hPD
    F χ u hχ hχc hχR hu heq
  have hD (x) (hx : x ∈ Ω) : fderiv ℝ (fderiv ℝ (globalC2Value U)) x =
      fderiv ℝ (fderiv ℝ u) x := by
    have hg : globalC2Value U =ᶠ[𝓝 x] u := by
      filter_upwards [hΩ.mem_nhds hx] with z hz
      rw [hU]
      change χ z * u z = u z
      rw [hχone z hz, one_mul]
    exact (hg.fderiv (𝕜 := ℝ)).fderiv_eq
  let H := globalHessianHolder hα.le U
  refine ⟨‖H‖ + 1, by positivity, ?_⟩
  intro x hx y hy
  have hh := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le H x y
  change ‖OAI.Analysis.Normed.Function.Holder.HolderMap.value (globalHessianHolder hα.le U) x -
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (globalHessianHolder hα.le U) y‖ ≤ ‖H‖ * (dist x y) ^ α at hh
  rw [globalHessianHolder_apply, globalHessianHolder_apply, hD x hx, hD y hy, dist_eq_norm] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _))

end OAI.Analysis.PDE.Schauder
