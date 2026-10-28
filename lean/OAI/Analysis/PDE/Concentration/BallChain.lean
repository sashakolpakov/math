import OAI.Analysis.PDE.Concentration.BallMean
import OAI.Analysis.PDE.Concentration.SmoothExtension
import OAI.Analysis.PDE.Concentration.CompactChain

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set Metric InnerProductSpace Laplacian Filter
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- Neighboring ball averages of a nonnegative superharmonic function are
comparable, with a constant independent of the function and the centers. -/
theorem exists_ball_overlap_constant {s : ℝ} (hs : 0 < s) : ∃ D : ℝ, 0 < D ∧
    ∀ (f : E → ℝ), ContDiff ℝ 2 f → ∀ (x x' : E), dist x' x ≤ s →
      (∀ y ∈ closedBall x (7 * s), 0 ≤ f y) →
      (∀ y ∈ closedBall x (7 * s), Δ f y ≤ 0) →
      (∫ y in closedBall x' s, f y) ≤ D * ∫ y in closedBall x s, f y := by
  obtain ⟨C, hC, hmean⟩ := exists_uniform_ball_mean_constant (E := E)
  let V : ℝ := volume.real (closedBall (0 : E) s)
  have hV : 0 < V := ENNReal.toReal_pos (measure_closedBall_pos volume 0 hs).ne'
    measure_closedBall_lt_top.ne
  let D : ℝ := C * (6 * s) ^ Module.finrank ℝ E / V
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro f hf x x' hdist hn hΔ
  have hsub {y : E} (hy : y ∈ closedBall x s) : closedBall y (6 * s) ⊆ closedBall x (7 * s) := by
    intro z hz
    have hzy : dist z y ≤ 6 * s := hz
    have hyx : dist y x ≤ s := hy
    change dist z x ≤ 7 * s
    linarith [dist_triangle z y x]
  have hpoint (y : E) (hy : y ∈ closedBall x s) :
      (∫ z in closedBall x' s, f z) ≤ C * (6 * s) ^ Module.finrank ℝ E * f y := by
    have ht : closedBall x' s ⊆ closedBall y (3 * s) := by
      intro z hz
      have hzx : dist z x' ≤ s := hz
      have hxy : dist x y ≤ s := by simpa only [mem_closedBall, dist_comm] using hy
      change dist z y ≤ 3 * s
      linarith [dist_triangle z x' y, dist_triangle x' x y]
    have hnb : ∀ z ∈ closedBall y (3 * s), 0 ≤ f z := by
      intro z hz
      apply hn z (hsub hy ?_)
      exact closedBall_subset_closedBall (by linarith) hz
    have hle : (∫ z in closedBall x' s, f z) ≤ ∫ z in closedBall y (3 * s), f z := by
      apply setIntegral_mono_set
        (hf.continuous.continuousOn.integrableOn_compact (isCompact_closedBall y (3 * s)))
      · filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
        exact hnb z hz
      · exact Eventually.of_forall ht
    have hb := hmean f hf y (6 * s) (by positivity)
      (fun z hz => hn z (hsub hy hz)) (fun z hz => hΔ z (hsub hy hz))
    have hhalf : 6 * s / 2 = 3 * s := by ring
    rw [hhalf] at hb
    exact hle.trans hb
  have hi : IntegrableOn f (closedBall x s) :=
    hf.continuous.continuousOn.integrableOn_compact (isCompact_closedBall x s)
  have : IsFiniteMeasure (volume.restrict (closedBall x s)) :=
    ⟨by simpa using (measure_closedBall_lt_top (μ := (volume : Measure E)) (x := x) (r := s))⟩
  have hmain := integral_mono_ae (μ := volume.restrict (closedBall x s))
    (integrable_const (∫ z in closedBall x' s, f z))
    (hi.const_mul (C * (6 * s) ^ Module.finrank ℝ E))
    (by filter_upwards [ae_restrict_mem measurableSet_closedBall] with y hy; exact hpoint y hy)
  rw [integral_const, integral_const_mul, smul_eq_mul] at hmain
  simp only [measureReal_def, Measure.restrict_apply_univ] at hmain
  rw [← measureReal_def, Measure.addHaar_real_closedBall_center] at hmain
  change V * (∫ z in closedBall x' s, f z) ≤
    C * (6 * s) ^ Module.finrank ℝ E * ∫ y in closedBall x s, f y at hmain
  dsimp [D]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hV).mpr
  nlinarith [hmain]

theorem exists_uniform_compact_ball_mixing
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {K : Set P} (hK : IsCompact K) (hc : Convex ℝ K)
    {φ : P → E} (hφ : ContinuousOn φ K) {s : ℝ} (hs : 0 < s) :
    ∃ M : ℝ, 0 < M ∧ ∀ f : E → ℝ, ContDiff ℝ 2 f →
      (∀ x ∈ φ '' K, ∀ y ∈ closedBall x (7 * s), 0 ≤ f y) →
      (∀ x ∈ φ '' K, ∀ y ∈ closedBall x (7 * s), Δ f y ≤ 0) →
      ∀ x ∈ φ '' K, ∀ z ∈ φ '' K, (∫ y in closedBall z s, f y) ≤ M * f x := by
  obtain ⟨N, _, hchains⟩ := compact_convex_image_uniform_chain hK hc hφ hs
  obtain ⟨D, hD, hover⟩ := exists_ball_overlap_constant (E := E) hs
  obtain ⟨C, hC, hmean⟩ := exists_uniform_ball_mean_constant (E := E)
  refine ⟨D ^ N * (C * (2 * s) ^ Module.finrank ℝ E), by positivity, ?_⟩
  intro f hf hn hΔ x hx z hz
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hz
  obtain ⟨γ, hγ0, hγN, hγK, hγdist⟩ := hchains p hp q hq
  have hiter : ∀ j ≤ N, (∫ y in closedBall (γ j) s, f y) ≤
      D ^ j * ∫ y in closedBall (γ 0) s, f y := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have hjN : j < N := Nat.lt_of_succ_le hj
      have hstep := hover f hf (γ j) (γ (j + 1)) (hγdist j hjN)
        (hn _ (hγK j hjN.le)) (hΔ _ (hγK j hjN.le))
      calc
        _ ≤ D * ∫ y in closedBall (γ j) s, f y := hstep
        _ ≤ D * (D ^ j * ∫ y in closedBall (γ 0) s, f y) :=
          mul_le_mul_of_nonneg_left (ih hjN.le) hD.le
        _ = _ := by rw [pow_succ]; ring
  have hstart := hmean f hf (φ p) (2 * s) (by positivity)
    (fun y hy => hn _ ⟨p, hp, rfl⟩ y (closedBall_subset_closedBall (by linarith) hy))
    (fun y hy => hΔ _ ⟨p, hp, rfl⟩ y (closedBall_subset_closedBall (by linarith) hy))
  have htwo : 2 * s / 2 = s := by ring
  rw [htwo] at hstart
  have hend := hiter N le_rfl
  rw [hγ0, hγN] at hend
  exact hend.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hstart (pow_nonneg hD.le N))

end OAI.Analysis.PDE.Concentration
