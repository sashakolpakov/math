import OAI.Analysis.PDE.Concentration.RegularizedDensity
import OAI.Analysis.Calculus.Current.Physical.Compact
import OAI.Analysis.Calculus.Current.Fiber.Bounds

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current _root_.MeasureTheory
open scoped Matrix Matrix.Norms.Elementwise

theorem transverseRatio_norm_le_one {d : ℕ} (a : ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ)
    (hr : OAI.Analysis.Calculus.Current.fiberDefining (1 / 10) a z ≤ 0) : ‖transverseRatio z‖ ≤ 1 := by
  have hb := OAI.Analysis.Calculus.Current.fiber_ratio_bound (1 / 10) a z (by norm_num) hr
  have he : ‖transverseRatio z‖ ^ 2 = ∑ i, ‖OAI.Analysis.Calculus.Current.ratio z i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  nlinarith [norm_nonneg (transverseRatio z)]

theorem physical_input_height {d : ℕ} (a : ℝ) (τ : ℂ)
    (q : Option (Fin d) → ℂ) (ha : 0 < a) (ht : a ≤ ‖τ‖) (ht' : ‖τ‖ ≤ 4 * a)
    (hr : OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0) :
    a ≤ ‖OAI.Analysis.Calculus.Current.physicalEmbedding τ q none‖ ∧ ‖OAI.Analysis.Calculus.Current.physicalEmbedding τ q none‖ ≤ 12 * a := by
  have h := OAI.Analysis.Calculus.Current.fiber_collar_height_bounds a (OAI.Analysis.Calculus.Current.physicalEmbedding τ q) ha
    (by simpa only [OAI.Analysis.Calculus.Current.imaginaryTime_physicalEmbedding] using ht) (hr.trans (by norm_num))
  rw [OAI.Analysis.Calculus.Current.imaginaryTime_physicalEmbedding] at h
  exact ⟨h.1, h.2.trans (by linarith)⟩

theorem timeComponent_fiberCofactor_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ), 0 < a → a ≤ ‖z none‖ →
      OAI.Analysis.Calculus.Current.fiberDefining (1 / 10) a z ≤ 0 →
      OAI.Analysis.Calculus.Current.timeComponent (OAI.Analysis.Calculus.Current.fiberCofactor (1 / 10) a z) ≤ C / a ^ (2 * (d + 1)) := by
  obtain ⟨C, hC, hb⟩ := OAI.Analysis.Calculus.Current.fiberCofactor_norm_bound d
  refine ⟨2 * C, by positivity, ?_⟩
  intro a z ha hay hr
  have hre (q : Quaternion ℝ) : |q.re| ≤ ‖q‖ := by
    have he := Quaternion.normSq_eq_norm_mul_self q
    rw [Quaternion.normSq_def'] at he
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK, norm_nonneg q]
  have he (i j : OAI.Analysis.Calculus.Current.Index d) : |(OAI.Analysis.Calculus.Current.fiberCofactor (1 / 10) a z i j).re| ≤ C / a ^ (2 * (d + 1)) :=
    (hre _).trans (((norm_le_pi_norm _ j).trans (norm_le_pi_norm _ i)).trans (hb a z ha hay hr))
  have h00 := abs_le.mp (he none none)
  have h01 := abs_le.mp (he none (some none))
  have h10 := abs_le.mp (he (some none) none)
  have h11 := abs_le.mp (he (some none) (some none))
  simp only [OAI.Analysis.Calculus.Current.timeComponent, Quaternion.re_add, Quaternion.re_sub]
  rw [mul_div_assoc]
  linarith [h00.2, h01.1, h10.1, h11.2]

end OAI.Analysis.PDE.Concentration
