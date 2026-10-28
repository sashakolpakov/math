import Mathlib

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory Set Metric Filter
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The norm can be replaced on a compact set away from the origin by a
globally smooth, compactly supported real function. -/
theorem exists_smooth_compact_norm_replacement {S : Set E} (hS : IsCompact S)
    (hz : (0 : E) ∉ S) :
    ∃ ρ : E → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ EqOn ρ (fun x => ‖x‖) S := by
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp (hS.isClosed.isOpen_compl.mem_nhds hz)
  obtain ⟨R, hR, hRS⟩ := hS.isBounded.exists_pos_norm_le
  let a : ContDiffBump (0 : E) :=
    { rIn := r / 4, rOut := r / 2, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let b : ContDiffBump (0 : E) :=
    { rIn := R + 1, rOut := R + 2, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let ρ : E → ℝ := fun x => b x * ((1 - a x) * ‖x‖)
  refine ⟨ρ, ?_, b.hasCompactSupport.mul_right, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    apply b.contDiffAt.mul
    by_cases hx : x = 0
    · subst x
      apply (show ContDiffAt ℝ ∞ (fun _ : E => (0 : ℝ)) 0 from contDiffAt_const).congr_of_eventuallyEq
      filter_upwards [a.eventuallyEq_one] with y hy
      simp only [hy, Pi.one_apply, sub_self, zero_mul]
    · exact (contDiffAt_const.sub a.contDiffAt).mul (contDiffAt_norm ℝ hx)
  · intro x hx
    have ha : a x = 0 := by
      apply a.zero_of_le_dist
      by_contra! hh
      have hm : x ∈ ball (0 : E) r := by
        rw [mem_ball]
        exact hh.trans (by dsimp [a]; linarith)
      exact hrs hm hx
    have hb : b x = 1 := by
      apply b.one_of_mem_closedBall
      rw [mem_closedBall, dist_zero_right]
      exact (hRS x hx).trans (by dsimp [b]; linarith)
    simp only [ρ, ha, hb, sub_zero, one_mul]

theorem schwartz_derivative_bound_upto (φ : SchwartzMap ℝ ℂ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ N, ∀ x, ‖iteratedFDeriv ℝ i φ x‖ ≤ C := by
  let C := ∑ i ∈ Finset.range (N + 1), SchwartzMap.seminorm ℝ 0 i φ
  refine ⟨C, Finset.sum_nonneg (fun i _ => apply_nonneg _ _), ?_⟩
  intro i hi x
  exact (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ φ i x).trans
    (Finset.single_le_sum (fun j _ => apply_nonneg _ _) (Finset.mem_range.mpr (by omega)))

omit [FiniteDimensional ℝ E] in
theorem norm_iteratedFDeriv_scaled_difference {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (r δ : ℝ) {i : ℕ} (hi : 1 ≤ i) (x : E) :
    ‖iteratedFDeriv ℝ i (fun y => (r - ρ y) / δ) x‖ =
      |δ⁻¹| * ‖iteratedFDeriv ℝ i ρ x‖ := by
  have he : (fun y => (r - ρ y) / δ) = δ⁻¹ • (fun y => r - ρ y) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [he, iteratedFDeriv_const_smul_apply]
  · change ‖δ⁻¹ • iteratedFDeriv ℝ i ((fun _ : E => r) - ρ) x‖ = _
    rw [iteratedFDeriv_sub_apply contDiffAt_const (hρ.of_le (by simp)).contDiffAt]
    simp only [iteratedFDeriv_const_of_ne (by omega : i ≠ 0), Pi.zero_apply, zero_sub, norm_smul,
      Real.norm_eq_abs, norm_neg]
  · exact (contDiffAt_const.sub hρ.contDiffAt).of_le (by simp)

omit [FiniteDimensional ℝ E] in
/-- The composition estimate keeps the singular dependence on the shell
width explicit; the radius parameter need not lie in a compact interval. -/
theorem scaled_composition_derivative_bound {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (φ : SchwartzMap ℝ ℂ) {N : ℕ} {B C : ℝ} (hB : 1 ≤ B)
    (hρB : ∀ i, 1 ≤ i → i ≤ N → ∀ x, ‖iteratedFDeriv ℝ i ρ x‖ ≤ B)
    (hφC : ∀ i ≤ N, ∀ x, ‖iteratedFDeriv ℝ i φ x‖ ≤ C)
    (r : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) {i : ℕ} (hi : i ≤ N) (x : E) :
    ‖iteratedFDeriv ℝ i (fun y => φ ((r - ρ y) / δ)) x‖ ≤
      (i.factorial : ℝ) * C * (B * δ⁻¹) ^ i := by
  have hinner : ContDiff ℝ ∞ (fun y => (r - ρ y) / δ) :=
    (contDiff_const.sub hρ).div_const δ
  apply norm_iteratedFDeriv_comp_le (φ.smooth ⊤) hinner (by simp) x
  · intro j hj
    exact hφC j (hj.trans hi) _
  · intro j hj hj'
    rw [norm_iteratedFDeriv_scaled_difference hρ r δ hj x, abs_of_pos (inv_pos.mpr hδ)]
    have hiδ : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).2 hδone
    have hpB : B ≤ B ^ j := le_self_pow₀ hB (by omega)
    have hpδ : δ⁻¹ ≤ (δ⁻¹) ^ j := le_self_pow₀ hiδ (by omega)
    calc
      _ ≤ δ⁻¹ * B := mul_le_mul_of_nonneg_left (hρB j hj (hj'.trans hi) x) (inv_nonneg.mpr hδ.le)
      _ ≤ (δ⁻¹) ^ j * B ^ j := mul_le_mul hpδ hpB (by positivity) (by linarith)
      _ = _ := by rw [mul_pow]; ring

omit [FiniteDimensional ℝ E] in
theorem uniform_scaled_shell_derivative_bound {ρ : E → ℝ} {b : E → ℂ}
    (hρ : ContDiff ℝ ∞ ρ) (hsρ : HasCompactSupport ρ)
    (hb : ContDiff ℝ ∞ b) (hsb : HasCompactSupport b)
    (φ : SchwartzMap ℝ ℂ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x,
      ‖iteratedFDeriv ℝ N (fun y => φ ((r - ρ y) / δ) * b y) x‖ ≤ C * (δ⁻¹) ^ N := by
  obtain ⟨B₀, hB₀, hρB⟩ := hsρ.exists_bound_iteratedFDeriv hρ N
  obtain ⟨D, hD, hbD⟩ := hsb.exists_bound_iteratedFDeriv hb N
  obtain ⟨A, hA, hφA⟩ := schwartz_derivative_bound_upto φ N
  let B := B₀ + 1
  let c : ℕ → ℝ := fun i => (N.choose i : ℝ) * ((i.factorial : ℝ) * A * B ^ i) * D
  have hc (i : ℕ) : 0 ≤ c i := by dsimp [c, B]; positivity
  refine ⟨∑ i ∈ Finset.range (N + 1), c i, Finset.sum_nonneg (fun i _ => hc i), ?_⟩
  intro r δ hδ hδone x
  have hiδ : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).2 hδone
  have hcomp : ContDiff ℝ ∞ (fun y => φ ((r - ρ y) / δ)) :=
    (φ.smooth ⊤).comp ((contDiff_const.sub hρ).div_const δ)
  calc
    _ ≤ ∑ i ∈ Finset.range (N + 1), (N.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y => φ ((r - ρ y) / δ)) x‖ *
          ‖iteratedFDeriv ℝ (N - i) b x‖ :=
      norm_iteratedFDeriv_mul_le hcomp hb x (by simp)
    _ ≤ ∑ i ∈ Finset.range (N + 1), c i * (δ⁻¹) ^ N := by
      apply Finset.sum_le_sum
      intro i hi
      have hiN : i ≤ N := by simpa using hi
      have hci := scaled_composition_derivative_bound hρ φ
        (show 1 ≤ B by dsimp [B]; linarith)
        (fun j _ hj y => (hρB j hj y).trans (by dsimp [B]; linarith))
        hφA r hδ hδone hiN x
      calc
        _ ≤ (N.choose i : ℝ) * ((i.factorial : ℝ) * A * (B * δ⁻¹) ^ i) * D :=
          mul_le_mul (mul_le_mul_of_nonneg_left hci (by positivity))
            (hbD (N - i) (Nat.sub_le _ _) x) (norm_nonneg _) (by positivity)
        _ = c i * (δ⁻¹) ^ i := by dsimp [c]; rw [mul_pow]; ring
        _ ≤ c i * (δ⁻¹) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hiδ hiN) (hc i)
    _ = _ := by rw [Finset.sum_mul]

noncomputable def annularShellSymbol (b : E → ℂ) (φ : SchwartzMap ℝ ℂ) (r δ : ℝ) : E → ℂ :=
  fun ξ => φ ((r - ‖ξ‖) / δ) * b ξ

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem annularShellSymbol_eq_replaced {b : E → ℂ} {ρ : E → ℝ}
    (he : EqOn ρ (fun x => ‖x‖) (tsupport b)) (φ : SchwartzMap ℝ ℂ) (r δ : ℝ) :
    annularShellSymbol b φ r δ = fun ξ => φ ((r - ρ ξ) / δ) * b ξ := by
  funext ξ
  by_cases hξ : b ξ = 0
  · simp [annularShellSymbol, hξ]
  · simp only [annularShellSymbol, he (subset_tsupport b hξ)]

theorem contDiff_annularShellSymbol {b : E → ℂ} (hb : ContDiff ℝ ∞ b)
    (hs : HasCompactSupport b) (hz : (0 : E) ∉ tsupport b)
    (φ : SchwartzMap ℝ ℂ) (r δ : ℝ) : ContDiff ℝ ∞ (annularShellSymbol b φ r δ) := by
  obtain ⟨ρ, hρ, _, he⟩ := exists_smooth_compact_norm_replacement hs hz
  rw [annularShellSymbol_eq_replaced he]
  exact ((φ.smooth ⊤).comp ((contDiff_const.sub hρ).div_const δ)).mul hb

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem hasCompactSupport_annularShellSymbol {b : E → ℂ} (hs : HasCompactSupport b)
    (φ : SchwartzMap ℝ ℂ) (r δ : ℝ) : HasCompactSupport (annularShellSymbol b φ r δ) := hs.mul_left

/-- Every prescribed derivative of the actual annular shell symbol has
a uniform polynomial bound in the reciprocal shell width. -/
theorem uniform_annularShell_derivative_bound {b : E → ℂ} (hb : ContDiff ℝ ∞ b)
    (hs : HasCompactSupport b) (hz : (0 : E) ∉ tsupport b)
    (φ : SchwartzMap ℝ ℂ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x,
      ‖iteratedFDeriv ℝ N (annularShellSymbol b φ r δ) x‖ ≤ C * (δ⁻¹) ^ N := by
  obtain ⟨ρ, hρ, hsρ, he⟩ := exists_smooth_compact_norm_replacement hs hz
  obtain ⟨C, hC, hbnd⟩ := uniform_scaled_shell_derivative_bound hρ hsρ hb hs φ N
  refine ⟨C, hC, ?_⟩
  intro r δ hδ hδone x
  rw [annularShellSymbol_eq_replaced he]
  exact hbnd r δ hδ hδone x

end OAI.Analysis.Fourier.WavePackets
