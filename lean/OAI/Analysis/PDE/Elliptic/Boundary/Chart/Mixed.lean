import OAI.Analysis.PDE.Elliptic.Boundary.Chart.UniformFields
import OAI.Analysis.PDE.Elliptic.Boundary.FlatJet

/-! All mixed flat-coordinate Hessian components obey one boundary Hölder
estimate.  The tangent-field and prescribed-data constants are derived by
compactness from the fixed chart, uniformly over the unit tangent ball. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter InnerProductSpace OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Topology

theorem log_equation_chart_mixed_holder {n : ℕ} [Nonempty (Fin n)]
    {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧
      ∀ (P G : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) (B : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ),
      ContDiff ℝ 3 P → ContDiff ℝ 3 G → ContDiff ℝ 3 B →
      ∀ V : ℝ, 0 ≤ V → ∃ C : ℝ, 0 < C ∧
      ∀ (v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4), ‖v‖ = 1 →
      (∀ z ∈ closedHalfBall v, (fun y => P (G y)) =ᶠ[𝓝 z] id) →
      ∀ (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ), ContDiff ℝ 3 u →
      (∀ z ∈ closedHalfBall v, ‖fderiv ℝ u (G z)‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖fderiv ℝ (gradient u) (G z)‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z))‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖pullbackEllipticOperator (fderiv ℝ P (G z))
        (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z)))‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ∀ w, lam * ‖w‖ ^ 2 ≤ inner ℝ w
        (pullbackEllipticOperator (fderiv ℝ P (G z))
          (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z))) w)) →
      (∀ z ∈ closedHalfBall v, ∀ w, inner ℝ w
        (pullbackEllipticOperator (fderiv ℝ P (G z))
          (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z))) w) ≤ L * ‖w‖ ^ 2) →
      (∀ z ∈ openHalfBall v, DifferentiableAt ℝ f (G z)) →
      (∀ z ∈ openHalfBall v, ‖fderiv ℝ f (G z)‖ / |f (G z)| ≤ V) →
      (∀ z ∈ openHalfBall v,
        (fun y => OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) =ᶠ[𝓝 (G z)] f) →
      (∀ z, ‖z‖ ≤ 2 → inner ℝ v z = 0 → u (G z) = B (G z)) →
      ∀ e, ‖e‖ ≤ 1 → inner ℝ v e = 0 →
      ∀ z z', ‖z‖ ≤ 1 / 8 → ‖z'‖ ≤ 1 / 8 → inner ℝ v z = 0 → inner ℝ v z' = 0 →
        |fderiv ℝ (fderiv ℝ (fun y => u (G y) - B (G y))) z v e -
          fderiv ℝ (fderiv ℝ (fun y => u (G y) - B (G y))) z' v e| ≤ C * ‖z - z'‖ ^ α := by
  obtain ⟨α, hα, hα1, hholder⟩ := log_equation_boundary_remainder_holder (n := n) hlam hL
  refine ⟨α, hα, hα1, ?_⟩
  intro P G B hP hG hB V hV
  let K := Metric.closedBall (0 : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) 1
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨CT, hCT, hbT⟩ := exists_uniform_chart_field_bounds hG hP hB (hK.image hG.continuous)
  have hc1 : Continuous (fun z => ‖iteratedFDeriv ℝ 1 G z‖) :=
    continuous_iff_continuousAt.mpr fun z => (hG.contDiffAt.continuousAt_iteratedFDeriv (by norm_num)).norm
  have hc2 : Continuous (fun z => ‖iteratedFDeriv ℝ 2 G z‖) :=
    continuous_iff_continuousAt.mpr fun z => (hG.contDiffAt.continuousAt_iteratedFDeriv (by norm_num)).norm
  obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn hc1.continuousOn
  obtain ⟨C2, hC2⟩ := hK.exists_bound_of_continuousOn hc2.continuousOn
  let W := max V (max CT (max C1 C2))
  have hVW : V ≤ W := le_max_left _ _
  have hTW : CT ≤ W := (le_max_left _ _).trans (le_max_right _ _)
  have h1W : C1 ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h2W : C2 ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨C, hC, hholder⟩ := hholder W (hV.trans hVW)
  refine ⟨C, hC, ?_⟩
  intro v hv hinv u f hu hDu hD2u hA hAA hlo hhi hf hf1 heq hzero e he hve
  have hTK (z) (hz : z ∈ closedHalfBall v) := hbT e he (G z) ⟨z, by simpa [K] using hz.1, rfl⟩
  have hG1 (z) (hz : z ∈ closedHalfBall v) : ‖fderiv ℝ G z‖ ≤ W := by
    have hh := hC1 z (by simpa [K] using hz.1)
    exact (by simpa [norm_iteratedFDeriv_one] using hh : ‖fderiv ℝ G z‖ ≤ C1).trans h1W
  have hG2 (z) (hz : z ∈ closedHalfBall v) : ‖iteratedFDeriv ℝ 2 G z‖ ≤ W := by
    exact (by simpa using hC2 z (by simpa [K] using hz.1) : ‖iteratedFDeriv ℝ 2 G z‖ ≤ C2).trans h2W
  have hfieldzero (z) (hz : ‖z‖ ≤ 1) (hvz : inner ℝ v z = 0) :
      fieldDerivative (fun y => u y - B y) (chartTangentField G P e) (G z) = 0 := by
    rw [chart_field_comp (hG.differentiable (by norm_num))
      ((hu.sub hB).differentiable (by norm_num)) e z ((hinv z ⟨hz, hvz.ge⟩).eq_of_nhds)]
    apply flat_boundary_first_jet_of_local_zero
      (((hu.sub hB).comp hG).differentiable (by norm_num) z) hv hvz hve
    have hz2 : z ∈ Metric.ball (0 : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) 2 := by simpa using (show ‖z‖ < 2 by linarith)
    filter_upwards [Metric.isOpen_ball.mem_nhds hz2] with y hy hyv
    exact sub_eq_zero.mpr (hzero y (by have := Metric.mem_ball.mp hy; simpa using this.le) hyv)
  have hn := hholder v hv P G (chartTangentField G P e) u B f hu hB
    (contDiff_chartTangentField hG hP e) (fun _ _ => (hG.of_le (by norm_num)).contDiffAt)
    (fun _ _ => hP.differentiable (by norm_num) _) hinv
    (fun z hz => (hDu z hz).trans hVW) (fun z hz => (hD2u z hz).trans hVW)
    (fun z hz => (hTK z hz).1.trans hTW) (fun z hz => (hTK z hz).2.1.trans hTW)
    (fun z hz => (hTK z hz).2.2.1.trans hTW) (fun z hz => (hTK z hz).2.2.2.1.trans hTW)
    (fun z hz => (hTK z hz).2.2.2.2.trans hTW) hG1 hG2
    (fun z hz => (hA z hz).trans hVW) (fun z hz => (hAA z hz).trans hVW)
    hlo hhi hf (fun z hz => (hf1 z hz).trans hVW) heq hfieldzero
  intro z z' hz hz' hvz hvz'
  have hzc : z ∈ closedHalfBall v := ⟨by linarith, hvz.ge⟩
  have hz'c : z' ∈ closedHalfBall v := ⟨by linarith, hvz'.ge⟩
  simpa only [chart_field_normal_eq hG hP (hu.sub hB) e v z (hinv z hzc),
    chart_field_normal_eq hG hP (hu.sub hB) e v z' (hinv z' hz'c)] using hn z z' hz hz' hvz hvz'

end OAI.Analysis.PDE.Elliptic
