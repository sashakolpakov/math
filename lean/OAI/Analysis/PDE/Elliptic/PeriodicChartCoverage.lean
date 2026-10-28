import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Coverage

/-! Physical neighborhoods covered by a fixed coordinate chart.  The
right-inverse identity is derived from the chart's left-inverse germ. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A left-inverse chart germ gives a genuine open physical neighborhood,
with inverse coordinates in any prescribed ball. -/
theorem exists_inverse_chart_neighborhood {P G : E → E} {a : E}
    (hP : ContDiff ℝ 3 P) (hG : ContDiff ℝ 3 G) (hG0 : G 0 = a)
    (hinv : (fun z => P (G z)) =ᶠ[𝓝 (0 : E)] id)
    {δ : ℝ} (hδ : 0 < δ) :
    P a = 0 ∧ ∃ R : ℝ, 0 < R ∧ ∃ V : Set E,
      IsOpen V ∧ a ∈ V ∧ Metric.closedBall a R ⊆ V ∧
      (∀ x ∈ V, G (P x) = x) ∧ MapsTo P V (Metric.ball 0 δ) := by
  have hPa : P a = 0 := by simpa [hG0] using hinv.eq_of_nhds
  have hleft : (fun x => G (P x)) =ᶠ[𝓝 a] id := by
    simpa only [hG0] using
      chart_local_left_inverse (hP.differentiable (by norm_num) (G 0)) hG hinv
  have hsmall : ∀ᶠ x in 𝓝 a, ‖P x‖ < δ := by
    have hc : ContinuousAt (fun x => ‖P x‖) a := hP.continuous.continuousAt.norm
    exact hc.tendsto.eventually
      (eventually_lt_nhds (by simpa only [hPa, norm_zero] using hδ))
  have hgood : ∀ᶠ x in 𝓝 a, G (P x) = x ∧ ‖P x‖ < δ := by
    filter_upwards [hleft, hsmall] with x hx hs
    exact ⟨hx, hs⟩
  obtain ⟨ε, hε, heps⟩ := Metric.mem_nhds_iff.mp hgood
  refine ⟨hPa, ε / 2, by positivity, Metric.ball a ε,
    Metric.isOpen_ball, Metric.mem_ball_self hε,
    Metric.closedBall_subset_ball (by linarith), ?_, ?_⟩
  · intro x hx
    exact (heps hx).1
  · intro x hx
    simpa only [Metric.mem_ball, dist_zero_right] using (heps hx).2

/-- The same fixed chart covers a physical closed ball and identifies the
sublevel side with the positive coordinate halfspace.  No inverse or coverage
assumption is added to the original left-inverse chart data. -/
theorem exists_coordinate_chart_coverage {m : ℕ} (k : Fin m)
    {P G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    {a : EuclideanSpace ℝ (Fin m)} {r : EuclideanSpace ℝ (Fin m) → ℝ}
    {c : ℝ} (hc : 0 < c)
    (hP : ContDiff ℝ 3 P) (hG : ContDiff ℝ 3 G) (hG0 : G 0 = a)
    (hinv : (fun z => P (G z)) =ᶠ[𝓝 (0 : EuclideanSpace ℝ (Fin m))] id)
    (hlevel : ∀ z ∈ Metric.closedBall 0 2, r (G z) - r a = -c * z k)
    (hra : r a = 0) {δ : ℝ} (hδ : 0 < δ) :
    P a = 0 ∧ ∃ R : ℝ, 0 < R ∧ ∃ V : Set (EuclideanSpace ℝ (Fin m)),
      IsOpen V ∧ a ∈ V ∧ Metric.closedBall a R ⊆ V ∧
      (∀ x ∈ V, G (P x) = x) ∧
      (∀ x ∈ V, r x = -c * (P x) k) ∧
      MapsTo P (Metric.closedBall a R ∩ {x | r x ≤ 0})
        (Metric.ball 0 δ ∩ {z | 0 ≤ z k}) := by
  obtain ⟨hPa, R, hR, V, hV, haV, hRV, hleft, hPV⟩ :=
    exists_inverse_chart_neighborhood hP hG hG0 hinv (lt_min hδ zero_lt_one)
  have hformula : ∀ x ∈ V, r x = -c * (P x) k := by
    intro x hx
    have hb : P x ∈ Metric.closedBall 0 2 := by
      have hsmall : ‖P x‖ < min δ 1 := by
        simpa only [Metric.mem_ball, dist_zero_right] using hPV hx
      have hnorm : ‖P x‖ ≤ 2 := by
        have := hsmall.trans_le (min_le_right δ 1)
        linarith
      simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm
    simpa only [hleft x hx, hra, sub_zero] using hlevel (P x) hb
  refine ⟨hPa, R, hR, V, hV, haV, hRV, hleft, hformula, ?_⟩
  intro x hx
  have hxV : x ∈ V := hRV hx.1
  refine ⟨?_, ?_⟩
  · exact Metric.ball_subset_ball (min_le_left δ 1) (hPV hxV)
  · change 0 ≤ (P x) k
    have hsub : r x ≤ 0 := hx.2
    rw [hformula x hxV] at hsub
    nlinarith

end OAI.Analysis.PDE.Elliptic
