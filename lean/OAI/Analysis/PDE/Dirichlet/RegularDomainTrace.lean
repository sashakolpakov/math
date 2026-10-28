import OAI.Analysis.PDE.Dirichlet.ChartDerivativeTrace
import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Constants
import OAI.Analysis.PDE.Elliptic.Boundary.Density
import OAI.Analysis.PDE.Elliptic.PeriodicChartCoverage

open Set Filter InnerProductSpace
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.PDE.Elliptic

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem openHalfBall_open (v : E) : IsOpen (OAI.Analysis.PDE.Elliptic.openHalfBall v) :=
  (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const (innerSL ℝ v).continuous)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem openHalfBall_convex (v : E) : Convex ℝ (OAI.Analysis.PDE.Elliptic.openHalfBall v) := by
  have he : OAI.Analysis.PDE.Elliptic.openHalfBall v = Metric.ball 0 1 ∩ (innerSL ℝ v) ⁻¹' Ioi 0 := by
    ext x
    simp [OAI.Analysis.PDE.Elliptic.openHalfBall, Metric.mem_ball, dist_zero_right]
  rw [he]
  exact (convex_ball _ _).inter ((convex_Ioi 0).linear_preimage (innerSL ℝ v).toLinearMap)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem closure_openHalfBall_subset (v : E) :
    closure (OAI.Analysis.PDE.Elliptic.openHalfBall v) ⊆ OAI.Analysis.PDE.Elliptic.closedHalfBall v := by
  apply closure_minimal
  · intro x hx
    exact ⟨hx.1.le, hx.2.le⟩
  exact (isClosed_le continuous_norm continuous_const).inter
    (isClosed_le continuous_const (innerSL ℝ v).continuous)

omit [Nontrivial E] [FiniteDimensional ℝ E] in
private theorem mem_closure_openHalfBall {v z : E} (hv : ‖v‖ = 1)
    (hn : ‖z‖ < 1) (hi : 0 ≤ inner ℝ v z) : z ∈ closure (OAI.Analysis.PDE.Elliptic.openHalfBall v) := by
  rcases hi.eq_or_lt with he | hp
  · exact OAI.Analysis.PDE.Elliptic.flat_boundary_mem_closure_halfBall hv hn he.symm
  · exact subset_closure ⟨hn, hp⟩

omit [Nontrivial E] in
/-- On a regular C³ sublevel domain, continuous traces of the interior
derivative are the actual derivatives within the closed domain. No
convexity of the physical domain or smooth extension of f is assumed. -/
theorem hasFDerivWithinAt_regular_sublevel_of_continuous_trace
    {r : E → ℝ} (hr : ContDiff ℝ 3 r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {f : E → F} {A : E → E →L[ℝ] F}
    (hf : ContinuousOn f {x | r x ≤ 0})
    (hA : ContinuousOn A {x | r x ≤ 0})
    (hd : ∀ x, r x < 0 → HasFDerivAt f (A x) x)
    {a : E} (ha : r a ≤ 0) :
    HasFDerivWithinAt f (A a) {x | r x ≤ 0} a := by
  by_cases hzero : r a = 0
  · obtain ⟨v, c, C, G, P, hv, hc, _, hG, hP, hG0, hchart⟩ :=
      OAI.Analysis.PDE.Elliptic.exists_bounded_normalized_chart hr a (hreg a hzero) isOpen_univ (mem_univ a)
    have hz : (0 : E) ∈ Metric.closedBall 0 2 := by simp
    obtain ⟨hPa, R, hR, V, hV, haV, _, hGP, hPV⟩ :=
      OAI.Analysis.PDE.Elliptic.exists_inverse_chart_neighborhood hP hG hG0 (hchart 0 hz).2.1
        (by norm_num : (0 : ℝ) < 1/2)
    have hball (z : E) (hz : ‖z‖ ≤ 1) : z ∈ Metric.closedBall 0 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using (hz.trans (by norm_num : (1 : ℝ) ≤ 2))
    have hlevel (z : E) (hz : ‖z‖ ≤ 1) : r (G z) = -c * inner ℝ v z := by
      simpa only [hzero, sub_zero] using (hchart z (hball z hz)).2.2.1
    have hGD : MapsTo G (closure (OAI.Analysis.PDE.Elliptic.openHalfBall v)) {x | r x ≤ 0} := by
      intro z hz
      have hh := closure_openHalfBall_subset v hz
      change r (G z) ≤ 0
      rw [hlevel z hh.1]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hh.2
    have hGΩ : MapsTo G (OAI.Analysis.PDE.Elliptic.openHalfBall v) {x | r x < 0} := by
      intro z hz
      change r (G z) < 0
      rw [hlevel z hz.1.le]
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos hc) hz.2
    have hPK : MapsTo P (V ∩ {x | r x ≤ 0}) (closure (OAI.Analysis.PDE.Elliptic.openHalfBall v)) := by
      intro y hy
      have hn : ‖P y‖ < 1/2 := by
        simpa only [Metric.mem_ball, dist_zero_right] using hPV hy.1
      have hn1 : ‖P y‖ < 1 := hn.trans (by norm_num)
      apply mem_closure_openHalfBall hv hn1
      have hval := hlevel (P y) hn1.le
      rw [hGP y hy.1] at hval
      have hnonpos : r y ≤ 0 := hy.2
      nlinarith
    have hK : V ∩ {x | r x ≤ 0} ∈ 𝓝[{x | r x ≤ 0}] a :=
      inter_mem (mem_nhdsWithin_of_mem_nhds (hV.mem_nhds haV)) self_mem_nhdsWithin
    have hinv : (fun x => G (P x)) =ᶠ[𝓝 a] id := by
      filter_upwards [hV.mem_nhds haV] with x hx
      exact hGP x hx
    have hPclosure : P a ∈ closure (OAI.Analysis.PDE.Elliptic.openHalfBall v) := by
      rw [hPa]
      exact mem_closure_openHalfBall hv (by simp) (by simp)
    exact hasFDerivWithinAt_of_chart_trace (openHalfBall_open v) (openHalfBall_convex v)
      (hG.of_le (by norm_num)) (hP.of_le (by norm_num)) hGD hGΩ hPK hPclosure hK hinv hf hA hd
  · exact (hd a (lt_of_le_of_ne ha hzero)).hasFDerivWithinAt

end OAI.Analysis.PDE.Dirichlet
