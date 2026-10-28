import OAI.Analysis.PDE.Schauder.Calculus.Boundary.Freeze

/-! Uniform coefficient freezing directly at the absorption threshold. -/

noncomputable section
open Set Metric
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem exists_uniform_absorbable_halfspace_freezing {m : ℕ} {α N P ρ : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hN : 0 ≤ N) (hP : 0 ≤ P) (hρ : 0 < ρ) :
    ∃ r > 0, r < ρ ∧
      ∀ A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α,
        ‖A‖ ≤ N → OAI.Analysis.Normed.Function.Holder.HolderMap.value A 0 = 1 →
        ∃ B : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α,
          ‖B‖ ≤ 1 ∧ P * (m : ℝ) * m * ‖B‖ * (1 + (3 : ℝ)^α) ≤ 1 / 2 ∧
          (∀ x, ‖x‖ ≤ 1 → 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = OAI.Analysis.Normed.Function.Holder.HolderMap.value A (r • x)) ∧
          (∀ x, x ∉ closedBall 0 2 → OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = 0) := by
  let D := P * (m : ℝ) * m * (1 + (3 : ℝ)^α)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  let ε := 1 / (2 * (D + 1))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hεone : ε ≤ 1 := by
    dsimp only [ε]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hDε : D * ε ≤ 1 / 2 := by
    change D * (1 / (2 * (D + 1))) ≤ 1 / 2
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  obtain ⟨r, hr, hrρ, hb⟩ := exists_uniform_halfspace_freezing hα hα1 hN hε hρ
  refine ⟨r, hr, hrρ, ?_⟩
  intro A hA hA0
  obtain ⟨B, hBn, hBval, hBs⟩ := hb A hA hA0
  refine ⟨B, hBn.le.trans hεone, ?_, hBval, hBs⟩
  calc
    _ = D * ‖B‖ := by dsimp only [D]; ring
    _ ≤ D * ε := mul_le_mul_of_nonneg_left hBn.le hD
    _ ≤ 1 / 2 := hDε

end OAI.Analysis.PDE.Schauder
