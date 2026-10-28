import OAI.Analysis.PDE.Schauder.Dirichlet.DriftCutoffSchauder
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.ScaledEquiv

noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

private theorem boundary_nested_radial_cutoff_data {m : ℕ} :
    let E := EuclideanSpace ℝ (Fin m)
    let χ : E → ℝ := radialCutoff (1/8)
    let η : E → ℝ := radialCutoff (1/2)
    ContDiff ℝ 3 χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ closedBall 0 1 ∧
    ContDiff ℝ 3 η ∧ HasCompactSupport η ∧ tsupport η ⊆ closedBall 0 1 ∧
    (∀ x ∈ tsupport χ, η =ᶠ[𝓝 x] fun _ => 1) := by
  let E := EuclideanSpace ℝ (Fin m)
  let χ : E → ℝ := radialCutoff (1/8)
  let η : E → ℝ := radialCutoff (1/2)
  have hχ : ContDiff ℝ 3 χ := (contDiff_radialCutoff _).of_le (by simp)
  have hχc : HasCompactSupport χ := hasCompactSupport_radialCutoff (by norm_num)
  have hχquarter : tsupport χ ⊆ closedBall 0 (1/4) := by
    simpa only [show (2 : ℝ)*(1/8) = 1/4 by norm_num] using
      (tsupport_radialCutoff_subset (E := E) (r := 1/8) (by norm_num))
  have hχR : tsupport χ ⊆ closedBall 0 1 := hχquarter.trans (closedBall_subset_closedBall (by norm_num))
  have hη : ContDiff ℝ 3 η := (contDiff_radialCutoff _).of_le (by simp)
  have hηc : HasCompactSupport η := hasCompactSupport_radialCutoff (by norm_num)
  have hηR : tsupport η ⊆ closedBall 0 1 := by
    simpa only [show (2 : ℝ)*(1/2) = 1 by norm_num] using
      (tsupport_radialCutoff_subset (E := E) (r := 1/2) (by norm_num))
  have hηone (x) (hx : x ∈ tsupport χ) : η =ᶠ[𝓝 x] fun _ => 1 := by
    have hxq : ‖x‖ ≤ 1/4 := by simpa only [mem_closedBall, dist_zero_right] using hχquarter hx
    have hb : ∀ᶠ y in 𝓝 x, y ∈ ball 0 (1/2) := isOpen_ball.mem_nhds (by
      simpa only [mem_ball, dist_zero_right] using (show ‖x‖ < (1/2 : ℝ) by linarith))
    filter_upwards [hb] with y hy
    exact radialCutoff_one (by norm_num) (le_of_lt (by simpa only [mem_ball, dist_zero_right] using hy))
  exact ⟨hχ, hχc, hχR, hη, hηc, hηR, hηone⟩


theorem halfspace_radial_schauder_with_drift {m : ℕ} (hm : 3 ≤ m) (k : Fin m)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ P > 0, ∀ N Nb ε : ℝ, 0 ≤ N → 0 ≤ Nb → 0 < ε → ∃ D > 0,
      ∀ B : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α,
      P * (m : ℝ) * m * ‖B‖ * (1 + (3 : ℝ)^α) ≤ 1 / 2 →
      ‖OAI.Analysis.Normed.Function.Holder.HolderMap.constant (1 : Matrix (Fin m) (Fin m) ℝ) - B‖ ≤ N →
      ∀ b : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m)) α,
      ‖b‖ ≤ Nb →
      ∀ u : EuclideanSpace ℝ (Fin m) → ℝ, ContDiff ℝ 3 u →
      (∀ x, ‖x‖ ≤ 1 → x k = 0 → u x = 0) →
      ∀ (F : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α) H M, 0 ≤ H → 0 ≤ M →
      (∀ x, ‖x‖ ≤ 1 → 0 ≤ x k → |u x| ≤ M) →
      (∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ (fun z => radialCutoff (1/2) z * u z)) x -
          fderiv ℝ (fderiv ℝ (fun z => radialCutoff (1/2) z * u z)) y‖ ≤ H * ‖x-y‖^α) →
      (∀ x, ‖x‖ ≤ 1 → 0 ≤ x k →
        nondivergenceOperator (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y) u x =
          OAI.Analysis.Normed.Function.Holder.HolderMap.value F x + fderiv ℝ u x (OAI.Analysis.Normed.Function.Holder.HolderMap.value b x)) →
      ∀ x ∈ ball 0 (1/8), 0 ≤ x k → ∀ y ∈ ball 0 (1/8), 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
          (ε * H + D * (‖F‖ + M)) * ‖x-y‖^α := by
  let E := EuclideanSpace ℝ (Fin m)
  let χ : E → ℝ := radialCutoff (1/8)
  let η : E → ℝ := radialCutoff (1/2)
  obtain ⟨hχ, hχc, hχR, hη, hηc, hηR, hηone⟩ := boundary_nested_radial_cutoff_data (m := m)
  obtain ⟨P, hP, hlocal⟩ := halfspace_nested_cutoff_schauder_with_drift hm k hα hα1 (show (0 : ℝ) < 1 by norm_num)
  refine ⟨P, hP, ?_⟩
  intro N Nb ε hN hNb hε
  obtain ⟨D, hD, hestimate⟩ := hlocal χ hχ hχc hχR N Nb ε hN hNb hε
  refine ⟨D, hD, ?_⟩
  intro B hsmall hBN b hbn u hu hz F H M hH hM hbound hh heq
  have hout := hestimate B (by simpa only [show (2 : ℝ)*1+1 = 3 by norm_num] using hsmall)
    hBN b hbn η hη hηc hηone
    (fun x _ => by rw [abs_of_nonneg (radialCutoff_nonneg _ _)]; exact radialCutoff_le_one _ _)
    u hu (by
      intro x hx hn
      exact hz x (by simpa only [mem_closedBall, dist_zero_right] using hηR (subset_closure hn)) hx)
    F H M hH hM (by
      intro x hx hxk
      exact hbound x (by simpa only [mem_closedBall, dist_zero_right] using hηR hx) hxk)
    hh (by
      intro x hx hn
      exact heq x (by simpa only [mem_closedBall, dist_zero_right] using hχR (subset_closure hn)) hx)
  intro x hx hxk y hy hyk
  have hxnorm : ‖x‖ < 1/8 := by simpa only [mem_ball, dist_zero_right] using hx
  have hynorm : ‖y‖ < 1/8 := by simpa only [mem_ball, dist_zero_right] using hy
  have hxy := hout x hxk y hyk
  rw [hessian_radialCutoff_mul_eq u (by norm_num) x hxnorm,
    hessian_radialCutoff_mul_eq u (by norm_num) y hynorm] at hxy
  exact hxy

end OAI.Analysis.PDE.Schauder
