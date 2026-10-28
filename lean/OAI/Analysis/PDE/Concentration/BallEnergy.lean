import OAI.Analysis.PDE.Concentration.BallBarrier
import OAI.Analysis.PDE.Concentration.BallDeterminant
import OAI.Analysis.PDE.Concentration.SpatialBarrier

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Matrix OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped MatrixOrder ComplexOrder

theorem density_root_mul (n : ℕ) {m : ℝ} (hm : 0 ≤ m) :
    m ^ (1 / ((n : ℝ) + 1)) * m = m ^ (((n : ℝ) + 2) / ((n : ℝ) + 1)) := by
  by_cases hz : m = 0
  · subst m
    rw [Real.zero_rpow (by positivity), zero_mul, Real.zero_rpow (by positivity)]
  · have hpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hz)
    calc
      _ = m ^ (1 / ((n : ℝ) + 1)) * m ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = m ^ (1 / ((n : ℝ) + 1) + 1) := (Real.rpow_add hpos _ _).symm
      _ = _ := by congr 1; field_simp; ring

/-- The source's pointwise output-energy gain, derived from the actual
quadratic barrier and nonlinear comparison on a full real fiber ball. -/
theorem exists_ball_energy_lower (n : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    ∃ c : ℝ, 0 < c ∧ ∀ (x₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3) (h lam m : ℝ),
      0 < h → 0 < lam → 0 ≤ m → m ≤ lam ^ (n + 1) →
      ∀ (B u μ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3 → ℝ),
      ContDiffOn ℝ 2 B (Metric.ball x₀ h) → ContDiffOn ℝ 2 u (Metric.ball x₀ h) →
      ContinuousOn B (Metric.closedBall x₀ h) → ContinuousOn u (Metric.closedBall x₀ h) →
      (∀ x ∈ Metric.ball x₀ h, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun y => B y + u y) x)).PosDef) →
      (∀ x ∈ Metric.ball x₀ h, ∃ v : Fin (n + 2) → Quaternion ℝ,
        OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots B x = lam • OAI.Analysis.Calculus.Quaternion.outer v ∧ (∑ i, (OAI.Analysis.Calculus.Quaternion.outer v i i).re) ≤ C) →
      (∀ x ∈ Metric.ball x₀ h, OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun y => B y + u y) x) = lam * μ x) →
      (∀ x ∈ Metric.ball x₀ h, m ≤ μ x) →
      (∀ x, ‖x - x₀‖ = h → u x ≤ 0) →
      c * h ^ 2 * m ^ (((n : ℝ) + 2) / ((n : ℝ) + 1)) ≤ (-u x₀) * μ x₀ := by
  obtain ⟨c, hc, hc1, hcoef⟩ := exists_quadratic_barrier_coefficient n hC
  refine ⟨c, hc, ?_⟩
  intro x₀ h lam m hh hlam hm hml B u μ hB hu hBc huc hpos hrank hPDE hμ hbd
  let α := c * m ^ (1 / ((n : ℝ) + 1))
  have hα : 0 ≤ α := mul_nonneg hc.le (Real.rpow_nonneg hm _)
  have hcoef' := (hcoef lam m hlam hm hml).2
  have hdet (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3) (hx : x ∈ Metric.ball x₀ h) :
      OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun y => B y + α * (‖y - x₀‖ ^ 2 - h ^ 2)) x) ≤
      OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun y => B y + u y) x) := by
    obtain ⟨v, hv, ht⟩ := hrank x hx
    have hb : ContDiffAt ℝ 2 B x := hB.contDiffAt (Metric.isOpen_ball.mem_nhds hx)
    have hr : ContDiffAt ℝ 2 (fun y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3 => ‖y - x₀‖ ^ 2 - h ^ 2) x :=
      (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).sub contDiff_const).contDiffAt
    have he := quaternionHessian_linear_combination_at OAI.Analysis.Calculus.Quaternion.threeSlots hb hr 1 α
    simp only [one_mul, quaternionHessian_three_ball, smul_smul, hv] at he
    rw [he, hPDE x hx]
    have hd := hcoef' v ht
    have hf : α * 6 = 6 * α := mul_comm _ _
    rw [hf]
    exact hd.trans (by nlinarith [mul_le_mul_of_nonneg_left (hμ x hx) hlam.le])
  have hb := ball_barrier_comparison (by omega) x₀ h α hh hB hu hBc huc hpos hdet hbd
  have hx₀ : x₀ ∈ Metric.ball x₀ h := Metric.mem_ball_self hh
  have hu₀ := hb x₀ (Metric.closedBall_subset_closedBall (le_refl h) (Metric.ball_subset_closedBall hx₀))
  simp only [sub_self, norm_zero, zero_pow (by omega : 2 ≠ 0), zero_sub] at hu₀
  have hneg : α * h ^ 2 ≤ -u x₀ := by nlinarith
  have hμ₀ : m ≤ μ x₀ := hμ x₀ hx₀
  calc
    c * h ^ 2 * m ^ (((n : ℝ) + 2) / ((n : ℝ) + 1)) = α * h ^ 2 * m := by
      rw [← density_root_mul n hm]
      dsimp only [α]
      ring
    _ ≤ α * h ^ 2 * μ x₀ := mul_le_mul_of_nonneg_left hμ₀ (by positivity)
    _ ≤ (-u x₀) * μ x₀ := mul_le_mul_of_nonneg_right hneg (hm.trans hμ₀)

end OAI.Analysis.PDE.Concentration
