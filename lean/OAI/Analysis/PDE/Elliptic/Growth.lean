import OAI.Analysis.PDE.Elliptic.LocalizedABP
import OAI.Analysis.PDE.Elliptic.GaussianBarrier

open Set _root_.MeasureTheory _root_.MeasureTheory.Measure
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- A low value anywhere in a fixed larger ball forces a positive
amount of a bounded sublevel set in the unit ball. -/
theorem uniform_sublevel_growth_large (μ : Measure E) [IsAddHaarMeasure μ]
    {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) {R : ℝ} (hR : 1 ≤ R) :
    ∃ M C : ℝ, 1 < M ∧ 0 < C ∧
      ∀ (A : E → E →L[ℝ] E) (u : E → ℝ), ContDiff ℝ 2 u →
      (∀ x ∈ Metric.closedBall (0 : E) (2 * R), 0 ≤ u x) →
      (∀ x ∈ Metric.closedBall (0 : E) (2 * R), ∀ v : E,
        lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      (∀ x ∈ Metric.closedBall (0 : E) (2 * R), ∀ v : E,
        inner ℝ v (A x v) ≤ L * ‖v‖ ^ 2) →
      (∀ x ∈ interior (Metric.closedBall (0 : E) (2 * R)), ellipticTrace A u x ≤ 0) →
      ∀ x₀ ∈ Metric.closedBall (0 : E) R, u x₀ ≤ 1 →
        μ (Metric.ball (0 : E) (1 / (4 * R))) ≤
          ENNReal.ofReal C * μ {x : E | ‖x‖ < 1 ∧ u x ≤ M} := by
  have hRpos : 0 < R := by linarith
  let d : ℝ := Module.finrank ℝ E
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E))
  let a : ℝ := L * d / (2 * lam) + 1
  have ha : 0 < a := by dsimp [a]; positivity
  have hscale : L * Module.finrank ℝ E ≤ 2 * a * lam * (1 : ℝ) ^ 2 := by
    have ht : L * d ≤ a * (2 * lam) := (div_le_iff₀ (by positivity)).mp (by dsimp [a]; linarith)
    dsimp [d] at ht
    nlinarith
  obtain ⟨eta, heta, hgap⟩ := gaussianBarrier_inner_gap (E := E) ha (r := R) (R := 2 * R)
    hRpos.le (by linarith)
  let c : ℝ := 2 / eta
  have hc : 0 < c := by dsimp [c]; positivity
  have hceta : c * eta = 2 := by dsimp [c]; field_simp
  let D : ℝ := c * (2 * a * (L * d))
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨c + 1, (D / lam) ^ Module.finrank ℝ E, by linarith, by positivity, ?_⟩
  intro A u hu hunonneg hlow hupp hLu x₀ hx₀ hux₀
  let K : Set E := Metric.closedBall 0 (2 * R)
  let w : E → ℝ := gaussianBarrier a (2 * R)
  let f : E → ℝ := fun x ↦ u x + c • w x
  have hw : ContDiff ℝ 2 w := (gaussianBarrier_contDiff a (2 * R)).of_le (by simp)
  have hf : ContDiff ℝ 2 f := hu.add (hw.const_smul c)
  have hxnorm : ‖x₀‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx₀
  have hxK : x₀ ∈ K := by
    change dist x₀ 0 ≤ 2 * R
    simpa only [dist_zero_right] using hxnorm.trans (by linarith)
  have hfsmall : f x₀ ≤ -1 := by
    have hg := mul_le_mul_of_nonneg_left (hgap x₀ hxnorm) hc.le
    change u x₀ + c * gaussianBarrier a (2 * R) x₀ ≤ -1
    nlinarith
  have hbd : ∀ x ∈ K, x ∉ interior K → 0 ≤ f x := by
    intro x hx hxi
    have hxn : ‖x‖ ≤ 2 * R := by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hx
    have hxe : ‖x‖ = 2 * R := by
      apply le_antisymm hxn
      by_contra hn
      have hxb : x ∈ Metric.ball (0 : E) (2 * R) := by
        simpa only [Metric.mem_ball, dist_zero_right] using lt_of_not_ge hn
      exact hxi ((interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball) hxb)
    have hwz : w x = 0 := gaussianBarrier_zero a (2 * R) hxe
    simpa only [f, hwz, smul_zero, add_zero] using hunonneg x hx
  have hrad : ∀ x ∈ K, ‖x - x₀‖ ≤ 4 * R := by
    intro x hx
    have hxn : ‖x‖ ≤ 2 * R := by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hx
    exact (norm_sub_le x x₀).trans (by linarith)
  have hLf (x : E) : ellipticTrace A f x = ellipticTrace A u x + c * ellipticTrace A w x :=
    ellipticTrace_add_smul A hu hw c x
  have hinside : ∀ x ∈ negativeContactSet K f, x ∈ Metric.ball (0 : E) 1 →
      ellipticTrace A f x ≤ D := by
    intro x hx _
    have hxK' : x ∈ K := interior_subset hx.1.1
    have hwupper := ellipticTrace_gaussianBarrier_upper A (2 * R) ha.le hlam.le hL.le x
      (hlow x hxK') (hupp x hxK')
    have h := mul_le_mul_of_nonneg_left hwupper hc.le
    rw [hLf]
    have hLu' := hLu x hx.1.1
    change ellipticTrace A u x + c * ellipticTrace A (gaussianBarrier a (2 * R)) x ≤ D
    dsimp [D, d]
    linarith
  have houtside : ∀ x ∈ negativeContactSet K f, x ∉ Metric.ball (0 : E) 1 →
      ellipticTrace A f x ≤ 0 := by
    intro x hx hxs
    have hxK' : x ∈ K := interior_subset hx.1.1
    have hxn : 1 ≤ ‖x‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hxs
    have hwneg := ellipticTrace_gaussianBarrier_nonpos A (2 * R) ha.le hlam.le hscale x
      (by nlinarith : (1 : ℝ) ^ 2 ≤ ‖x‖ ^ 2) (hlow x hxK') (hupp x hxK')
    rw [hLf]
    exact add_nonpos (hLu x hx.1.1) (mul_nonpos_of_nonneg_of_nonpos hc.le hwneg)
  have habp := abp_localized_forcing μ (isCompact_closedBall (0 : E) (2 * R)) hf hxK
    (by linarith : f x₀ < 0) hbd (by positivity : (0 : ℝ) < 4 * R) hrad A hlam
    (fun x hx ↦ hlow x (interior_subset hx.1.1)) Metric.isOpen_ball.measurableSet hD.le hinside houtside
  have hsub : negativeContactSet K f ∩ Metric.ball (0 : E) 1 ⊆
      {x : E | ‖x‖ < 1 ∧ u x ≤ c + 1} := by
    intro x hx
    refine ⟨by simpa only [Metric.mem_ball, dist_zero_right] using hx.2, ?_⟩
    have hfneg : u x + c * w x < 0 := hx.1.2
    have hwlower := mul_le_mul_of_nonneg_left (gaussianBarrier_lower ha.le (2 * R) x) hc.le
    change c * (-1) ≤ c * w x at hwlower
    nlinarith
  calc
    μ (Metric.ball (0 : E) (1 / (4 * R))) ≤ μ (Metric.ball (0 : E) (-f x₀ / (4 * R))) :=
      measure_mono (Metric.ball_subset_ball (by gcongr; linarith))
    _ ≤ _ := habp
    _ ≤ ENNReal.ofReal (D / lam) ^ Module.finrank ℝ E * μ {x : E | ‖x‖ < 1 ∧ u x ≤ c + 1} :=
      mul_le_mul_of_nonneg_left (measure_mono hsub) zero_le
    _ = _ := by rw [ENNReal.ofReal_pow (div_pos hD hlam).le]

/-- Unit-ball specialization of the quantitative growth lemma. -/
theorem uniform_sublevel_growth (μ : Measure E) [IsAddHaarMeasure μ]
    {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    ∃ M C : ℝ, 1 < M ∧ 0 < C ∧
      ∀ (A : E → E →L[ℝ] E) (u : E → ℝ), ContDiff ℝ 2 u →
      (∀ x ∈ Metric.closedBall (0 : E) 2, 0 ≤ u x) →
      (∀ x ∈ Metric.closedBall (0 : E) 2, ∀ v : E,
        lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      (∀ x ∈ Metric.closedBall (0 : E) 2, ∀ v : E,
        inner ℝ v (A x v) ≤ L * ‖v‖ ^ 2) →
      (∀ x ∈ interior (Metric.closedBall (0 : E) 2), ellipticTrace A u x ≤ 0) →
      ∀ x₀ ∈ Metric.closedBall (0 : E) 1, u x₀ ≤ 1 →
        μ (Metric.ball (0 : E) (1 / 4)) ≤
          ENNReal.ofReal C * μ {x : E | ‖x‖ < 1 ∧ u x ≤ M} := by
  simpa using uniform_sublevel_growth_large μ hlam hL (R := 1) le_rfl

end OAI.Analysis.PDE.Elliptic
