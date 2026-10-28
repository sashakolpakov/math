import OAI.Analysis.PDE.Elliptic.Boundary.ClosedFixed
import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Coverage

/-! Full C²,α control on the closed sublevel set near a regular boundary
point. The chart, its bounds, and all approach estimates are derived. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter InnerProductSpace OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Topology Matrix ComplexOrder

theorem closed_hessian_holder_near_regular_level {n : ℕ}
    {r B : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4 → ℝ} (hr : ContDiff ℝ 3 r) (hB : ContDiff ℝ 3 B)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4) (hrx : r x = 0) (hreg : fderiv ℝ r x ≠ 0)
    {U : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4)} (hU : IsOpen U) (hxU : x ∈ U)
    {lam V L₁ L₂ : ℝ} (hlam : 0 < lam) (hV : 0 < V) (hLV : lam ≤ V)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) :
    ∃ ρ α C : ℝ, 0 < ρ ∧ 0 < α ∧ α < 1 ∧ 0 < C ∧
      ∀ (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4 → ℝ), ContDiff ℝ 4 u → Continuous f →
      (∀ y ∈ U, r y ≤ 0 → ‖fderiv ℝ u y‖ ≤ V) →
      (∀ y ∈ U, r y ≤ 0 → ‖fderiv ℝ (gradient u) y‖ ≤ V) →
      (∀ y ∈ U, r y ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)).PosDef) →
      (∀ y ∈ U, r y ≤ 0 → ‖OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)‖ ≤ V) →
      (∀ y ∈ U, r y ≤ 0 → ∀ w, lam * ‖w‖ ^ 2 ≤ inner ℝ w
        (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y) w)) →
      (∀ y ∈ U, r y ≤ 0 → DifferentiableAt ℝ f y) →
      (∀ y ∈ U, r y ≤ 0 → f y ≠ 0) →
      (∀ y ∈ U, r y ≤ 0 → ‖fderiv ℝ f y‖ / |f y| ≤ V) →
      (∀ y ∈ U, r y < 0 → OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y) = f y) →
      (∀ y ∈ U ∩ {z | r z < 0}, ∀ z ∈ U ∩ {z | r z < 0},
        |Real.log (f y) - Real.log (f z)| ≤ L₁ * dist y z) →
      (∀ y ∈ U ∩ {z | r z < 0}, ∀ v,
        -L₂ * ‖v‖ ^ 2 ≤ deriv (deriv (fun t : ℝ => Real.log (f (y + t • v)))) 0) →
      (∀ y ∈ U, r y = 0 → u y = B y) →
      ∀ y ∈ Metric.closedBall x ρ, r y ≤ 0 →
      ∀ y' ∈ Metric.closedBall x ρ, r y' ≤ 0 →
        ‖fderiv ℝ (gradient u) y - fderiv ℝ (gradient u) y'‖ ≤ C * ‖y - y'‖ ^ α := by
  obtain ⟨v, c, C0, G, P, hv, hc, hC0, hG, hP, hG0, hchart⟩ :=
    exists_bounded_normalized_chart hr x hreg hU hxU
  have hC0p : 0 < C0 := lt_of_lt_of_le zero_lt_one hC0
  have hmem (z) (hz : z ∈ closedHalfBall v) : z ∈ Metric.closedBall (0 : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4) 2 := by
    have hh : ‖z‖ ≤ 2 := by linarith [hz.1]
    simpa using hh
  have hinv (z) (hz : z ∈ closedHalfBall v) := (hchart z (hmem z hz)).2.1
  have hrG (z) (hz : z ∈ closedHalfBall v) : r (G z) = -c * inner ℝ v z := by
    simpa only [hrx, sub_zero] using (hchart z (hmem z hz)).2.2.1
  obtain ⟨α, Cb, hα, hα1, hCb, hholder⟩ := log_equation_closed_fixed_chart_holder
    (hr.of_le (by norm_num)) hB hG hP hv hU
    (fun z hz => (hchart z (hmem z hz)).1)
    hc hlam hLV hL₁ hL₂ hV hC0p hrG hinv
    (fun z hz => (hchart z (hmem z hz)).2.2.2.2.2.2)
    (fun z hz => (hchart z (hmem z hz)).2.2.2.1)
    (fun z hz => (hchart z (hmem z hz)).2.2.2.2.1)
    (fun z hz => (hchart z (hmem z hz)).2.2.2.2.2.1)
  obtain ⟨ρ, Lp, hρ, hLp, hcover, hLip⟩ := exists_chart_coverage hP hG hG0
    ((hchart 0 (by simp)).2.1)
  refine ⟨ρ, α, Cb * Lp ^ α, hρ, hα, hα1, mul_pos hCb (Real.rpow_pos_of_pos hLp _), ?_⟩
  intro u f hu hf hDu hD2u hpos hA hlo hdf hfne hf1 heq hlog hlog₂ hzero
  have hactive (z) (hz : z ∈ closedHalfBall v) : G z ∈ U ∧ r (G z) ≤ 0 := by
    have hh := hchart z (hmem z hz)
    refine ⟨hh.1, ?_⟩
    have hl := hh.2.2.1
    rw [hrx, sub_zero] at hl
    rw [hl]
    nlinarith [hz.2]
  have hgz (z) (hz : ‖z‖ ≤ 2) (hvz : inner ℝ v z = 0) : u (G z) = B (G z) := by
    have hh := hchart z (by simpa using hz)
    apply hzero (G z) hh.1
    have hl := hh.2.2.1
    simpa [hrx, hvz] using hl
  have hupper (y) (hy : y ∈ U) (hry : r y ≤ 0) (w : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4) :
      inner ℝ w (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y) w) ≤ V * ‖w‖ ^ 2 := by
    apply (real_inner_le_norm _ _).trans
    have hh := (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)).le_opNorm w
    have hh' := hh.trans (mul_le_mul_of_nonneg_right (hA y hy hry) (norm_nonneg w))
    nlinarith [mul_le_mul_of_nonneg_left hh' (norm_nonneg w)]
  have hest := hholder u f hu hf
    (fun y hy => hpos y hy.1 hy.2.le)
    (fun y hy => heq y hy.1 hy.2)
    (fun y hy w => by
      rw [← OAI.Analysis.PDE.Dirichlet.logRealOperator_symbol]
      exact ⟨hlo y hy.1 hy.2.le w, hupper y hy.1 hy.2.le w⟩)
    (fun y hy => by
      simpa only [norm_fderiv_gradient (hu.of_le (by norm_num))] using hD2u y hy.1 hy.2.le)
    hlog hlog₂
    (fun z hz => hDu _ (hactive z hz).1 (hactive z hz).2)
    (fun z hz => hD2u _ (hactive z hz).1 (hactive z hz).2)
    (fun z hz => hpos _ (hactive z hz).1 (hactive z hz).2)
    (fun z hz => hlo _ (hactive z hz).1 (hactive z hz).2)
    (fun z hz => hA _ (hactive z hz).1 (hactive z hz).2)
    (fun z hz => hdf _ (hactive z hz).1 (hactive z hz).2)
    (fun z hz => hfne _ (hactive z hz).1 (hactive z hz).2)
    (fun z hz => hf1 _ (hactive z hz).1 (hactive z hz).2) hgz
  intro y hy hry y' hy' hry'
  have hcy := hcover y hy
  have hcy' := hcover y' hy'
  have hflat (a) (ha : a ∈ Metric.closedBall x ρ) (hra : r a ≤ 0) : 0 ≤ inner ℝ v (P a) := by
    have hca := hcover a ha
    have hh := (hchart (P a) (by have := hca.2; simpa using (show ‖P a‖ ≤ 2 by linarith))).2.2.1
    rw [hca.1, hrx, sub_zero] at hh
    nlinarith
  have hh := hest (P y) (P y') hcy.2 hcy'.2 (hflat y hy hry) (hflat y' hy' hry')
  rw [hcy.1, hcy'.1] at hh
  calc
    _ ≤ Cb * ‖P y - P y'‖ ^ α := hh
    _ ≤ Cb * (Lp * ‖y - y'‖) ^ α := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (hLip y hy y' hy') hα.le) hCb.le
    _ = (Cb * Lp ^ α) * ‖y - y'‖ ^ α := by rw [Real.mul_rpow hLp.le (norm_nonneg _)]; ring

end OAI.Analysis.PDE.Elliptic
