import OAI.Analysis.Calculus.Current.Physical.Fiber

/-! Compact physical fibers and a nonsingular collar. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

theorem fiber_collar_ratio_bound {d : ℕ} (a : ℝ) (z : Index d → ℂ)
    (hr : fiberDefining (1 / 10) a z ≤ 1) :
    (∑ i, ‖ratio z i‖ ^ 2) ≤ (1 / 50 : ℝ) := by
  rw [fiberDefining_formula] at hr
  have hp : 0 ≤ 100 * ‖phi z‖ ^ 2 / a ^ 2 := by positivity
  norm_num at hr
  linarith

theorem fiber_collar_phase_bound {d : ℕ} (a : ℝ) (z : Index d → ℂ) (ha : 0 < a)
    (hr : fiberDefining (1 / 10) a z ≤ 1) : ‖phi z‖ ≤ a / 5 := by
  rw [fiberDefining_formula] at hr
  have hW : 0 ≤ (∑ i, ‖ratio z i‖ ^ 2) / (1 / 10 : ℝ) ^ 2 := by positivity
  have hp : 100 * ‖phi z‖ ^ 2 / a ^ 2 ≤ 2 := by linarith
  have hp' := (div_le_iff₀ (sq_pos_of_pos ha)).mp hp
  nlinarith [norm_nonneg (phi z)]

theorem fiber_collar_denominator_bounds {d : ℕ} (a : ℝ) (z : Index d → ℂ)
    (hr : fiberDefining (1 / 10) a z ≤ 1) :
    (99 / 100 : ℝ) ≤ ‖fiberDenominator (ratio z)‖ ∧
      ‖fiberDenominator (ratio z)‖ ≤ (101 / 100 : ℝ) := by
  have hQ := (norm_fiberQuadratic_le (ratio z)).trans (fiber_collar_ratio_bound a z hr)
  have hq : ‖fiberQuadratic (ratio z) / 2‖ ≤ (1 / 100 : ℝ) := by
    rw [norm_div]
    norm_num
    linarith
  have hu := norm_add_le (1 : ℂ) (fiberQuadratic (ratio z) / 2)
  have hl := norm_sub_norm_le (1 : ℂ) (-(fiberQuadratic (ratio z) / 2))
  simp only [norm_one, norm_neg, sub_neg_eq_add] at hu hl
  change (99 / 100 : ℝ) ≤ ‖1 + fiberQuadratic (ratio z) / 2‖ ∧
    ‖1 + fiberQuadratic (ratio z) / 2‖ ≤ (101 / 100 : ℝ)
  constructor <;> linarith

theorem fiber_collar_height_bounds {d : ℕ} (a : ℝ) (z : Index d → ℂ) (ha : 0 < a)
    (ht : a ≤ ‖imaginaryTime z‖) (hr : fiberDefining (1 / 10) a z ≤ 1) :
    a ≤ ‖z none‖ ∧ ‖z none‖ ≤ 3 * ‖imaginaryTime z‖ := by
  have hP := fiber_collar_phase_bound a z ha hr
  obtain ⟨hDl, hDu⟩ := fiber_collar_denominator_bounds a z hr
  have he : z none - z (some none) = fiberDenominator (ratio z) * z none - phi z := by
    linear_combination -(fiberDenominator_mul_height z)
  have hT : ‖z none - z (some none)‖ ≤ ‖fiberDenominator (ratio z)‖ * ‖z none‖ + ‖phi z‖ := by
    rw [he]
    simpa only [norm_mul] using norm_sub_le (fiberDenominator (ratio z) * z none) (phi z)
  have hY : ‖fiberDenominator (ratio z)‖ * ‖z none‖ ≤ ‖z none - z (some none)‖ + ‖phi z‖ := by
    rw [← norm_mul, fiberDenominator_mul_height]
    exact norm_add_le _ _
  rw [imaginaryTime_norm] at hT hY
  have hsl : (7 / 5 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hsu : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_iff]; norm_num
  have hTlower := mul_le_mul_of_nonneg_left hsl (norm_nonneg (imaginaryTime z))
  have hTupper := mul_le_mul_of_nonneg_left hsu (norm_nonneg (imaginaryTime z))
  have hDlower := mul_le_mul_of_nonneg_right hDl (norm_nonneg (z none))
  have hDupper := mul_le_mul_of_nonneg_right hDu (norm_nonneg (z none))
  constructor <;> nlinarith

theorem physicalEmbedding_first {d : ℕ} (τ : ℂ) (q : Option (Fin d) → ℂ) :
    Real.sqrt 2 • physicalEmbedding τ q none - τ = q none := by
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  simp [physicalEmbedding, physicalLift, physicalTimeOffset, smul_add, hs]

theorem physical_fiber_collar_norm_bound {d : ℕ} (a : ℝ) (τ : ℂ)
    (q : Option (Fin d) → ℂ) (ha : 0 < a) (ht : a ≤ ‖τ‖)
    (hr : physicalFiberDefining (1 / 10) a τ q ≤ 1) : ‖q‖ ≤ 7 * ‖τ‖ := by
  let z := physicalEmbedding τ q
  have htime : imaginaryTime z = τ := imaginaryTime_physicalEmbedding τ q
  obtain ⟨hyl, hyu⟩ := fiber_collar_height_bounds a z ha (by simpa only [htime] using ht) hr
  rw [htime] at hyu
  have hY : z none ≠ 0 := norm_ne_zero_iff.mp (ha.trans_le hyl).ne'
  have hW := fiber_collar_ratio_bound a z hr
  have hsu : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_iff]; norm_num
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro b
  cases b with
  | none =>
    rw [← physicalEmbedding_first τ q]
    calc
      _ ≤ ‖Real.sqrt 2 • z none‖ + ‖τ‖ := norm_sub_le _ _
      _ ≤ 2 * ‖z none‖ + ‖τ‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        gcongr
      _ ≤ _ := by linarith
  | some i =>
    have hi : ‖ratio z i‖ ^ 2 ≤ ∑ j, ‖ratio z j‖ ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖ratio z j‖) (Finset.mem_univ i)
    have hi' : ‖ratio z i‖ ≤ 1 := by nlinarith [norm_nonneg (ratio z i)]
    have he : q (some i) = ratio z i * z none := by
      calc
        q (some i) = z (some (some i)) := by
          simp [z, physicalEmbedding, physicalLift, physicalTimeOffset]
        _ = ratio z i * z none := by simp [ratio, hY]
    rw [he, norm_mul]
    have hb := mul_le_mul_of_nonneg_right hi' (norm_nonneg (z none))
    nlinarith [norm_nonneg τ]

theorem isClosed_physical_fiber_sublevel {d : ℕ} (a : ℝ) (τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) (b : ℝ) (hb : b ≤ 1) :
    IsClosed {q : Option (Fin d) → ℂ | physicalFiberDefining (1 / 10) a τ q ≤ b} := by
  let S : Set (Option (Fin d) → ℂ) := {q | a ≤ ‖physicalEmbedding τ q none‖}
  have hS : IsClosed S := isClosed_le continuous_const
    (((continuous_apply none).comp (contDiff_physicalEmbedding τ).continuous).norm)
  have hc : ContinuousOn (physicalFiberDefining (1 / 10) a τ) S := by
    intro q hq
    exact (contDiffAt_physicalFiberDefining (1 / 10) a τ q
      (norm_ne_zero_iff.mp (ha.trans_le hq).ne')).continuousAt.continuousWithinAt
  have he : {q : Option (Fin d) → ℂ | physicalFiberDefining (1 / 10) a τ q ≤ b} =
      {q ∈ S | physicalFiberDefining (1 / 10) a τ q ≤ b} := by
    ext q
    constructor
    · intro hq
      refine ⟨?_, hq⟩
      exact (fiber_collar_height_bounds a (physicalEmbedding τ q) ha
        (by simpa only [imaginaryTime_physicalEmbedding] using ht) (hq.trans hb)).1
    · exact fun hq => hq.2
  rw [he]
  exact hS.isClosed_le hc continuousOn_const

theorem isCompact_physical_fiber_sublevel {d : ℕ} (a : ℝ) (τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) (b : ℝ) (hb : b ≤ 1) :
    IsCompact {q : Option (Fin d) → ℂ | physicalFiberDefining (1 / 10) a τ q ≤ b} := by
  apply (isCompact_closedBall (0 : Option (Fin d) → ℂ) (7 * ‖τ‖)).of_isClosed_subset
    (isClosed_physical_fiber_sublevel a τ ha ht b hb)
  intro q hq
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    physical_fiber_collar_norm_bound a τ q ha ht (hq.trans hb)

/-- A compact collar, uniformly separated from both rational singularity loci. -/
theorem physical_fiber_collar_separation {d : ℕ} (a : ℝ) (τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) (q : Option (Fin d) → ℂ)
    (hr : physicalFiberDefining (1 / 10) a τ q ≤ 1) :
    a ≤ ‖physicalEmbedding τ q none‖ ∧
      (99 / 100 : ℝ) ≤ ‖fiberDenominator (ratio (physicalEmbedding τ q))‖ :=
  ⟨(fiber_collar_height_bounds a (physicalEmbedding τ q) ha
      (by simpa only [imaginaryTime_physicalEmbedding] using ht) hr).1,
    (fiber_collar_denominator_bounds a (physicalEmbedding τ q) hr).1⟩

def physicalRegularDomain {d : ℕ} (τ : ℂ) : Set (Option (Fin d) → ℂ) :=
  {q | physicalEmbedding τ q none ≠ 0 ∧ fiberDenominator (ratio (physicalEmbedding τ q)) ≠ 0}

theorem isOpen_physicalRegularDomain {d : ℕ} (τ : ℂ) :
    IsOpen (physicalRegularDomain (d := d) τ) := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  have hY : ContinuousAt (fun p => physicalEmbedding τ p none) q :=
    ((continuous_apply none).comp (contDiff_physicalEmbedding τ).continuous).continuousAt
  have hQ : ContinuousAt (fun z : Index d → ℂ => fiberDenominator (ratio z))
      (physicalEmbedding τ q) := by
    have hp : ContDiffAt ℝ ⊤ (fun z : Index d → ℂ => fiberQuadratic (ratio z))
        (physicalEmbedding τ q) := by
      apply ContDiffAt.sum
      intro i _
      exact (contDiffAt_ratio _ hq.1 i).mul (contDiffAt_ratio _ hq.1 i)
    exact (contDiffAt_const.add (hp.div_const 2)).continuousAt
  have hD := hQ.comp (contDiff_physicalEmbedding τ).continuous.continuousAt
  exact Filter.inter_mem (hY.eventually_ne hq.1) (hD.eventually_ne hq.2)

theorem physical_fiber_collar_subset_regular {d : ℕ} (a : ℝ) (τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) :
    {q : Option (Fin d) → ℂ | physicalFiberDefining (1 / 10) a τ q ≤ 1} ⊆
      physicalRegularDomain τ := by
  intro q hq
  obtain ⟨hy, hd⟩ := physical_fiber_collar_separation a τ ha ht q hq
  exact ⟨norm_ne_zero_iff.mp (ha.trans_le hy).ne',
    norm_ne_zero_iff.mp (show 0 < ‖fiberDenominator (ratio (physicalEmbedding τ q))‖ by linarith).ne'⟩

theorem contDiffOn_physicalFiberDefining {d : ℕ} (w a : ℝ) (τ : ℂ) :
    ContDiffOn ℝ ⊤ (physicalFiberDefining (d := d) w a τ) (physicalRegularDomain τ) :=
  fun q hq => (contDiffAt_physicalFiberDefining w a τ q hq.1).contDiffWithinAt

theorem contDiffOn_physicalRadialField {d : ℕ} (τ : ℂ) :
    ContDiffOn ℝ ⊤ (physicalRadialField (d := d) τ) (physicalRegularDomain τ) :=
  fun q hq => (contDiffAt_physicalRadialField τ q hq.1 hq.2).contDiffWithinAt

end OAI.Analysis.Calculus.Current
