import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Constants
import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Bounds

/-! The normalized IFT charts cover genuine physical neighborhoods, and
their inverse coordinates are Lipschitz there. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem chart_local_left_inverse {P G : E → E} {z : E}
    (hP : DifferentiableAt ℝ P (G z)) (hG : ContDiff ℝ 3 G)
    (hinv : (fun y => P (G y)) =ᶠ[𝓝 z] id) :
    (fun y => G (P y)) =ᶠ[𝓝 (G z)] id := by
  have hJ := chart_jacobians_inverse hP (hG.differentiable (by norm_num) z) hinv
  let A : E ≃L[ℝ] E := ContinuousLinearEquiv.equivOfInverse (fderiv ℝ G z) (fderiv ℝ P (G z))
    (fun y => congrArg (fun L : E →L[ℝ] E => L y) hJ.1)
    (fun y => congrArg (fun L : E →L[ℝ] E => L y) hJ.2)
  have ha : HasStrictFDerivAt G (A : E →L[ℝ] E) z :=
    hG.hasStrictFDerivAt (by norm_num)
  have heq := ha.localInverse_unique hinv
  filter_upwards [heq, ha.eventually_right_inverse] with y hy hy'
  rw [hy]
  exact hy'

theorem exists_chart_coverage {P G : E → E} {x : E}
    (hP : ContDiff ℝ 3 P) (hG : ContDiff ℝ 3 G) (hG0 : G 0 = x)
    (hinv : (fun y => P (G y)) =ᶠ[𝓝 (0 : E)] id) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧
      (∀ y ∈ Metric.closedBall x ρ, G (P y) = y ∧ ‖P y‖ ≤ 1 / 8) ∧
      (∀ y ∈ Metric.closedBall x ρ, ∀ y' ∈ Metric.closedBall x ρ,
        ‖P y - P y'‖ ≤ C * ‖y - y'‖) := by
  have hPx : P x = 0 := by simpa [hG0] using hinv.eq_of_nhds
  have hleft : (fun y => G (P y)) =ᶠ[𝓝 x] id := by
    simpa only [hG0] using chart_local_left_inverse (hP.differentiable (by norm_num) (G 0)) hG hinv
  have hsmall : ∀ᶠ y in 𝓝 x, ‖P y‖ < 1 / 8 := by
    have hc : ContinuousAt (fun y => ‖P y‖) x := (hP.contDiffAt (x := x)).continuousAt.norm
    exact hc.tendsto.eventually (eventually_lt_nhds (by rw [hPx, norm_zero]; norm_num))
  obtain ⟨C, hC, hbound⟩ := eventually_C3_derivative_bounds (hP.contDiffAt (x := x))
  have hgood : ∀ᶠ y in 𝓝 x, G (P y) = y ∧ ‖P y‖ < 1 / 8 ∧ ‖fderiv ℝ P y‖ ≤ C := by
    filter_upwards [hleft, hsmall, hbound] with y hy hs hb
    exact ⟨hy, hs, hb.2.1⟩
  obtain ⟨ε, hε, heps⟩ := Metric.mem_nhds_iff.mp hgood
  refine ⟨ε / 2, C, by positivity, hC, ?_, ?_⟩
  · intro y hy
    have hh := heps (Metric.closedBall_subset_ball (by linarith : ε / 2 < ε) hy)
    exact ⟨hh.1, hh.2.1.le⟩
  · intro y hy y' hy'
    apply Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z (_ : z ∈ Metric.closedBall x (ε / 2)) => hP.differentiable (by norm_num) z)
      _ (convex_closedBall _ _) hy' hy
    intro z hz
    exact (heps (Metric.closedBall_subset_ball (by linarith : ε / 2 < ε) hz)).2.2

end OAI.Analysis.PDE.Elliptic
