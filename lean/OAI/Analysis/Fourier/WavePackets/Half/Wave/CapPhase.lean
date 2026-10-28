import OAI.Analysis.Fourier.WavePackets.AngularRescaling

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter
open scoped ContDiff Topology RealInnerProductSpace

def capAxis {d : ℕ} (c : Fin d → ℝ) : Space (d+1) :=
  WithLp.toLp 2 (Fin.cases 1 c)

def capTransverse {d : ℕ} (ξ : Space (d+1)) : Space (d+1) :=
  WithLp.toLp 2 (Fin.cases 0 (fun i => ξ i.succ))

@[simp] theorem capAxis_zero {d : ℕ} (c : Fin d → ℝ) : capAxis c 0 = 1 := rfl
@[simp] theorem capAxis_succ {d : ℕ} (c : Fin d → ℝ) (i : Fin d) : capAxis c i.succ = c i := by
  simp [capAxis]
@[simp] theorem capTransverse_zero {d : ℕ} (ξ : Space (d+1)) : capTransverse ξ 0 = 0 := rfl
@[simp] theorem capTransverse_succ {d : ℕ} (ξ : Space (d+1)) (i : Fin d) :
    capTransverse ξ i.succ = ξ i.succ := by simp [capTransverse]

theorem capAxis_ne_zero {d : ℕ} (c : Fin d → ℝ) : capAxis c ≠ 0 := by
  intro h
  have := congrArg (fun z : Space (d+1) => z 0) h
  simp at this

theorem angularChartRescale_eq_axis {d : ℕ} (γ : ℝ) (c : Fin d → ℝ) (ξ : Space (d+1)) :
    angularChartRescale γ c ξ = (ξ 0) • capAxis c + γ • capTransverse ξ := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp only [angularChartRescale_succ,PiLp.add_apply,PiLp.smul_apply,
      capAxis_succ,capTransverse_succ,smul_eq_mul]
    ring

def capLinearPhase {d : ℕ} (γ : ℝ) (c : Fin d → ℝ) (ξ : Space (d+1)) : ℝ :=
  (ξ 0)*‖capAxis c‖ + γ*(inner ℝ (capAxis c) (capTransverse ξ)/‖capAxis c‖)

/-- A twice-rationalized phase remainder. Unlike division by γ², this
formula is smooth at γ=0 on the positive axial half-space. -/
def capPhaseRemainder {d : ℕ} (γ : ℝ) (c : Fin d → ℝ) (ξ : Space (d+1)) : ℝ :=
  let r := (ξ 0)*‖capAxis c‖
  let q := inner ℝ (capAxis c) (capTransverse ξ)/‖capAxis c‖
  let D := ‖angularChartRescale γ c ξ‖+r
  ‖capTransverse ξ‖^2/D-q*(2*r*q+γ*‖capTransverse ξ‖^2)/D^2

private theorem quadratic_remainder_identity (N r q b γ : ℝ)
    (hD : N+r ≠ 0) (hsq : N^2 = r^2+2*γ*r*q+γ^2*b) :
    N-r-γ*q = γ^2*(b/(N+r)-q*(2*r*q+γ*b)/(N+r)^2) := by
  field_simp
  linear_combination (N+r-γ*q)*hsq

theorem norm_angularChartRescale_expansion {d : ℕ} (γ : ℝ) (c : Fin d → ℝ)
    (ξ : Space (d+1)) :
    ‖angularChartRescale γ c ξ‖^2 = ((ξ 0)*‖capAxis c‖)^2 +
      2*γ*((ξ 0)*‖capAxis c‖)*(inner ℝ (capAxis c) (capTransverse ξ)/‖capAxis c‖) +
      γ^2*‖capTransverse ξ‖^2 := by
  rw [angularChartRescale_eq_axis, norm_add_sq_real]
  simp only [norm_smul,Real.norm_eq_abs,real_inner_smul_left,real_inner_smul_right,
    mul_pow,sq_abs]
  have hc : ‖capAxis c‖ ≠ 0 := norm_ne_zero_iff.mpr (capAxis_ne_zero c)
  field_simp


/-- The exact quadratic cancellation used in the √h cap argument. -/
theorem capPhaseRemainder_identity {d : ℕ} (γ : ℝ) (c : Fin d → ℝ)
    (ξ : Space (d+1)) (hξ : 0 < ξ 0) :
    ‖angularChartRescale γ c ξ‖-capLinearPhase γ c ξ = γ^2*capPhaseRemainder γ c ξ := by
  have hr : 0 < (ξ 0)*‖capAxis c‖ := mul_pos hξ (norm_pos_iff.mpr (capAxis_ne_zero c))
  have hD : ‖angularChartRescale γ c ξ‖+(ξ 0)*‖capAxis c‖ ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (norm_nonneg _) hr)
  simpa only [capLinearPhase,capPhaseRemainder,sub_add_eq_sub_sub] using
    quadratic_remainder_identity _ _ _ _ γ hD (norm_angularChartRescale_expansion γ c ξ)

theorem contDiff_capAxis (d : ℕ) : ContDiff ℝ ∞ (@capAxis d) := by
  apply (contDiff_piLp 2).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : Fin d → ℝ => (1 : ℝ)))
  · simpa using (contDiff_apply ℝ ℝ j : ContDiff ℝ ∞ (fun c : Fin d → ℝ => c j))

theorem contDiff_capTransverse (d : ℕ) : ContDiff ℝ ∞ (@capTransverse d) := by
  apply (contDiff_piLp 2).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : Space (d+1) => (0 : ℝ)))
  · simpa using (show ContDiff ℝ ∞ (fun ξ : Space (d+1) => ξ j.succ) by fun_prop)

end OAI.Analysis.Fourier.WavePackets
