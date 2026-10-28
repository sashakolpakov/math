import OAI.Analysis.PDE.Elliptic.Boundary.FixedChart
import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Coverage

/-! A genuine physical-neighborhood boundary C²,α estimate.  The constants
are uniform over solutions and densities with the stated C²/ellipticity
and first-density-derivative bounds. The chart is constructed from r. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter InnerProductSpace OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Topology Matrix ComplexOrder

theorem boundary_hessian_holder_near_regular_level {n : ℕ} [Nonempty (Fin n)]
    {r B : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} (hr : ContDiff ℝ 3 r) (hB : ContDiff ℝ 3 B)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) (hrx : r x = 0) (hreg : fderiv ℝ r x ≠ 0)
    {U : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)} (hU : IsOpen U) (hxU : x ∈ U)
    {lam V : ℝ} (hlam : 0 < lam) (hV : 0 < V) :
    ∃ ρ α C : ℝ, 0 < ρ ∧ 0 < α ∧ α < 1 ∧ 0 < C ∧
      ∀ (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ), ContDiff ℝ 3 u → Continuous f →
      (∀ y ∈ U, r y ≤ 0 → ‖fderiv ℝ u y‖ ≤ V) →
      (∀ y ∈ U, r y ≤ 0 → ‖fderiv ℝ (gradient u) y‖ ≤ V) →
      (∀ y ∈ U, r y ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)).PosDef) →
      (∀ y ∈ U, r y ≤ 0 → ‖OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)‖ ≤ V) →
      (∀ y ∈ U, r y ≤ 0 → ∀ w, lam * ‖w‖ ^ 2 ≤ inner ℝ w
        (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y) w)) →
      (∀ y ∈ U, r y ≤ 0 → DifferentiableAt ℝ f y) →
      (∀ y ∈ U, r y ≤ 0 → f y ≠ 0) →
      (∀ y ∈ U, r y ≤ 0 → ‖fderiv ℝ f y‖ / |f y| ≤ V) →
      (∀ y ∈ U, r y < 0 → OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y) = f y) →
      (∀ y ∈ U, r y = 0 → u y = B y) →
      ∀ y ∈ Metric.closedBall x ρ, r y = 0 →
      ∀ y' ∈ Metric.closedBall x ρ, r y' = 0 →
        ‖fderiv ℝ (gradient u) y - fderiv ℝ (gradient u) y'‖ ≤ C * ‖y - y'‖ ^ α := by
  obtain ⟨v, c, C0, G, P, hv, hc, hC0, hG, hP, hG0, hchart⟩ :=
    exists_bounded_normalized_chart hr x hreg hU hxU
  have hC0p : 0 < C0 := lt_of_lt_of_le zero_lt_one hC0
  have hmem (z) (hz : z ∈ closedHalfBall v) : z ∈ Metric.closedBall (0 : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) 2 := by
    have hh : ‖z‖ ≤ 2 := by linarith [hz.1]
    simpa using hh
  have hinv (z) (hz : z ∈ closedHalfBall v) := (hchart z (hmem z hz)).2.1
  obtain ⟨α, Cb, hα, hα1, hCb, hholder⟩ := log_equation_boundary_fixed_chart_holder
    hlam hV hC0p P G B hP hG hB v hv hinv
    (fun z hz => (hchart z (hmem z hz)).2.2.2.2.2.2)
    (fun z hz => (hchart z (hmem z hz)).2.2.2.1)
    (fun z hz => (hchart z (hmem z hz)).2.2.2.2.1)
    (fun z hz => (hchart z (hmem z hz)).2.2.2.2.2.1)
  obtain ⟨ρ, Lp, hρ, hLp, hcover, hLip⟩ := exists_chart_coverage hP hG hG0
    ((hchart 0 (by simp)).2.1)
  refine ⟨ρ, α, Cb * Lp ^ α, hρ, hα, hα1, mul_pos hCb (Real.rpow_pos_of_pos hLp _), ?_⟩
  intro u f hu hf hDu hD2u hpos hA hlo hdf hfne hf1 heq hzero
  have hactive (z) (hz : z ∈ closedHalfBall v) : G z ∈ U ∧ r (G z) ≤ 0 := by
    have hh := hchart z (hmem z hz)
    refine ⟨hh.1, ?_⟩
    have hl := hh.2.2.1
    rw [hrx, sub_zero] at hl
    rw [hl]
    nlinarith [hz.2]
  have hstrict (z) (hz : z ∈ openHalfBall v) : G z ∈ U ∧ r (G z) < 0 := by
    have hzc : z ∈ closedHalfBall v := ⟨hz.1.le, hz.2.le⟩
    have hh := hchart z (hmem z hzc)
    refine ⟨hh.1, ?_⟩
    have hl := hh.2.2.1
    rw [hrx, sub_zero] at hl
    rw [hl]
    nlinarith [hz.2]
  have hgeq (z) (hz : z ∈ openHalfBall v) :
      (fun y => OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) =ᶠ[𝓝 (G z)] f := by
    have hh := (hU.inter (isOpen_lt hr.continuous continuous_const)).mem_nhds (hstrict z hz)
    filter_upwards [hh] with y hy
    exact heq y hy.1 hy.2
  have hgz (z) (hz : ‖z‖ ≤ 2) (hvz : inner ℝ v z = 0) : u (G z) = B (G z) := by
    have hh := hchart z (by simpa using hz)
    apply hzero (G z) hh.1
    have hl := hh.2.2.1
    simpa [hrx, hvz] using hl
  have hest := hholder u f hu hf
    (fun z hz => hDu _ (hactive z hz).1 (hactive z hz).2)
    (fun z hz => hD2u _ (hactive z hz).1 (hactive z hz).2)
    (fun z hz => hpos _ (hactive z hz).1 (hactive z hz).2)
    (fun z hz => hA _ (hactive z hz).1 (hactive z hz).2)
    (fun z hz => hlo _ (hactive z hz).1 (hactive z hz).2)
    (fun z hz => hdf _ (hactive z hz).1 (hactive z hz).2)
    (fun z hz => hfne _ (hactive z hz).1 (hactive z hz).2)
    (fun z hz => hf1 _ (hactive z hz).1 (hactive z hz).2) hgeq hgz
  intro y hy hry y' hy' hry'
  have hcy := hcover y hy
  have hcy' := hcover y' hy'
  have hflat (a) (ha : a ∈ Metric.closedBall x ρ) (hra : r a = 0) : inner ℝ v (P a) = 0 := by
    have hca := hcover a ha
    have hh := (hchart (P a) (by have := hca.2; simpa using (show ‖P a‖ ≤ 2 by linarith))).2.2.1
    rw [hca.1, hra, hrx] at hh
    nlinarith
  have hh := hest (P y) (P y') hcy.2 hcy'.2 (hflat y hy hry) (hflat y' hy' hry')
  rw [hcy.1, hcy'.1] at hh
  calc
    _ ≤ Cb * ‖P y - P y'‖ ^ α := hh
    _ ≤ Cb * (Lp * ‖y - y'‖) ^ α := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (hLip y hy y' hy') hα.le) hCb.le
    _ = (Cb * Lp ^ α) * ‖y - y'‖ ^ α := by rw [Real.mul_rpow hLp.le (norm_nonneg _)]; ring

end OAI.Analysis.PDE.Elliptic
