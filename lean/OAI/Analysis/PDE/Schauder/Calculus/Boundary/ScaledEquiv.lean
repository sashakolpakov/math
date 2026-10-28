import OAI.Analysis.PDE.Schauder.Calculus.Boundary.Unnormalize
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.Normalization

/-! Quantitative affine geometry for normalized boundary balls. -/

noncomputable section
open Set Metric Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

theorem tsupport_radialCutoff_subset {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {r : ℝ} (hr : 0 < r) : tsupport (radialCutoff (E := E) r) ⊆ closedBall 0 (2 * r) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  simp only [mem_closedBall, dist_zero_right]
  by_contra hn
  exact hx (radialCutoff_zero hr (le_of_lt (lt_of_not_ge hn)))

def scaledLinearEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E ≃L[ℝ] E) {r : ℝ} (hr : r ≠ 0) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.equivOfInverse
    (r • L.toContinuousLinearMap) (r⁻¹ • L.symm.toContinuousLinearMap)
    (fun y => by simp [map_smul, smul_smul, hr])
    (fun y => by simp [map_smul, smul_smul, hr])

@[simp] theorem scaledLinearEquiv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E ≃L[ℝ] E) {r : ℝ} (hr : r ≠ 0) (x) : scaledLinearEquiv L hr x = L (r • x) := by
  change r • L x = L (r • x)
  rw [map_smul]

theorem norm_scaledLinearEquiv_inv_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E ≃L[ℝ] E) {r N : ℝ} (hr : 0 < r) (hN : ‖L.symm.toContinuousLinearMap‖ ≤ N) :
    ‖(scaledLinearEquiv L hr.ne').symm.toContinuousLinearMap‖ ≤ r⁻¹ * N := by
  change ‖r⁻¹ • L.symm.toContinuousLinearMap‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  exact mul_le_mul_of_nonneg_left hN (inv_nonneg.mpr hr.le)

theorem norm_scaledLinearEquiv_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E ≃L[ℝ] E) {r N : ℝ} (hr : 0 < r) (hN : ‖L.toContinuousLinearMap‖ ≤ N) :
    ‖(scaledLinearEquiv L hr.ne').toContinuousLinearMap‖ ≤ r * N := by
  change ‖r • L.toContinuousLinearMap‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  exact mul_le_mul_of_nonneg_left hN hr.le

theorem scaled_boundary_affine_mem_ball {m : ℕ}
    (L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (x₀ : EuclideanSpace ℝ (Fin m)) {r N ρ : ℝ}
    (hr : 0 < r) (hN : 0 ≤ N) (hLn : ‖L.toContinuousLinearMap‖ ≤ N)
    (hrρ : r < ρ / (N + 1)) (x : EuclideanSpace ℝ (Fin m)) (hx : ‖x‖ ≤ 1) :
    x₀ + L (r • x) ∈ ball x₀ ρ := by
  change ‖x₀ + L (r • x) - x₀‖ < ρ
  rw [add_sub_cancel_left]
  have hbound : r * (N + 1) < ρ := (lt_div_iff₀ (by positivity)).mp hrρ
  calc
    _ ≤ ‖L.toContinuousLinearMap‖ * ‖r • x‖ := L.toContinuousLinearMap.le_opNorm _
    _ ≤ N * r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      calc
        _ ≤ N * (r * 1) := by gcongr
        _ = _ := by ring
    _ < ρ := by nlinarith

theorem scaled_boundary_affine_coordinate {m : ℕ} (k : Fin m)
    (L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (x₀ : EuclideanSpace ℝ (Fin m)) (hx₀ : x₀ k = 0) {r c : ℝ}
    (hnormal : ∀ x, L x k = c * x k) (x : EuclideanSpace ℝ (Fin m)) :
    (x₀ + L (r • x)) k = (r * c) * x k := by
  simp only [PiLp.add_apply, hnormal, hx₀, zero_add, PiLp.smul_apply, smul_eq_mul]
  ring

theorem hessian_radialCutoff_mul_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u : E → ℝ) {r : ℝ} (hr : 0 < r) (x : E) (hx : ‖x‖ < r) :
    fderiv ℝ (fderiv ℝ (fun y => radialCutoff r y * u y)) x = fderiv ℝ (fderiv ℝ u) x := by
  have he : (fun y => radialCutoff r y * u y) =ᶠ[𝓝 x] u := by
    have hb : ∀ᶠ y in 𝓝 x, y ∈ ball 0 r := isOpen_ball.mem_nhds (by simpa using hx)
    filter_upwards [hb] with y hy
    rw [radialCutoff_one hr (le_of_lt (by simpa only [mem_ball, dist_zero_right] using hy)), one_mul]
  exact ((he.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)).eq_of_nhds

end OAI.Analysis.PDE.Schauder
