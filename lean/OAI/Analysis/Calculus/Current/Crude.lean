import OAI.Analysis.Calculus.Current.Fiber.Bounds

/-! Dimension-uniform-in-scale crude size estimates for the actual current. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open OAI.Analysis.Calculus.Quaternion _root_.MeasureTheory
open scoped Matrix Matrix.Norms.Elementwise

theorem sourceWavePart_norm_le {d : ℕ} {ι : Type*} [Fintype ι]
    (h a R C : ℝ) (hh : 0 < h) (hR0 : 0 ≤ R) (hC0 : 0 ≤ C)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (hκ : ∀ j, 0 < κ j)
    (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0)
    (hR : ∀ j, κ j / ‖z none‖ ≤ R) (hC : ∀ j, ‖(⟨cR j, cI j⟩ : ℂ)‖ ≤ C)
    (hv : ∀ j, (∑ i, |v j i| ^ 2) ≤ 1 / 1600)
    (hr : fiberDefining (1 / 10) a z ≤ 0) :
    ‖sourceWavePart h a κ cR cI v x z‖ ≤ ((Fintype.card ι : ℝ) * ((d : ℝ) + 1) *
      (R ^ ((d : ℝ) / 2) * C)) ^ 2 := by
  let := periodizedKernelMeasure_isProbability d h hh
  apply (cutoffCurrent_norm_le a _ x z).trans
  have hpoint (t : SpatialCube d) := waveCurrent_norm_le_parameters
    κ cR cI v R C 0 hκ hR0 hC0 (x + cubeSpatialShift t) z hY hR hC
    (fun j i => velocity_coordinate_le_one (v j) (hv j) i)
    (fiber_ratio_coordinate_le_one a z hr)
    (fun j => mul_nonneg (div_nonneg (mul_nonneg (hκ j).le (norm_nonneg _)) (by norm_num))
      (Finset.sum_nonneg fun i _ => sq_nonneg _))
  have hn := norm_integral_le_of_norm_le_const (μ := periodizedKernelMeasure d h)
    (Filter.Eventually.of_forall hpoint)
  simpa [sourceWavePart, averagedWaveCurrent, measureReal_def] using! hn

theorem frequency_over_height_bound (h K κ y : ℝ) (hh : 0 < h)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ K / h) (hy : h ≤ y) : κ / y ≤ K / h ^ 2 := by
  calc
    _ ≤ κ / h := div_le_div_of_nonneg_left hκ0 hh hy
    _ ≤ (K / h) / h := div_le_div_of_nonneg_right hκ hh.le
    _ = _ := by ring

theorem scale_rpow_half (h K : ℝ) (d : ℕ) (hh : 0 < h) (hK : 0 ≤ K) :
    (K / h ^ 2) ^ ((d : ℝ) / 2) = K ^ ((d : ℝ) / 2) / h ^ d := by
  rw [Real.div_rpow hK (sq_nonneg h), ← Real.rpow_natCast_mul hh.le]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * ((d : ℝ) / 2) = d by ring, Real.rpow_natCast]

theorem sourceWavePart_crude_bound {d : ℕ} {ι : Type*} [Fintype ι]
    (h a N K C : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (_ : 0 ≤ N) (hK : 0 ≤ K) (hC0 : 0 ≤ C)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (hκ : ∀ j, 0 < κ j)
    (x : Index d → ℝ) (z : Index d → ℂ) (hy : h ≤ ‖z none‖)
    (hcount : (Fintype.card ι : ℝ) ≤ N / h ^ (d + 1))
    (hfreq : ∀ j, κ j ≤ K / h) (hC : ∀ j, ‖(⟨cR j, cI j⟩ : ℂ)‖ ≤ C)
    (hv : ∀ j, (∑ i, |v j i| ^ 2) ≤ 1 / 1600)
    (hr : fiberDefining (1 / 10) a z ≤ 0) :
    ‖sourceWavePart h a κ cR cI v x z‖ ≤
      (N * ((d : ℝ) + 1) * (K ^ ((d : ℝ) / 2) * C)) ^ 2 / h ^ (5 * (d + 1)) := by
  have hY : z none ≠ 0 := norm_pos_iff.mp (hh.trans_le hy)
  have hb := sourceWavePart_norm_le h a (K / h ^ 2) C hh (by positivity) hC0
    κ cR cI v hκ x z hY (fun j => frequency_over_height_bound h K (κ j) _ hh
      (hκ j).le (hfreq j) hy) hC hv hr
  rw [scale_rpow_half h K d hh hK] at hb
  have hcount' := mul_le_mul_of_nonneg_right hcount
    (show 0 ≤ ((d : ℝ) + 1) * (K ^ ((d : ℝ) / 2) / h ^ d * C) by positivity)
  have hbase : (Fintype.card ι : ℝ) * ((d : ℝ) + 1) *
      (K ^ ((d : ℝ) / 2) / h ^ d * C) ≤
      N * ((d : ℝ) + 1) * (K ^ ((d : ℝ) / 2) * C) / h ^ (2 * d + 1) := by
    convert hcount' using 1
    · ring
    · rw [show 2 * d + 1 = (d + 1) + d by omega, pow_add]
      ring
  have hsq := pow_le_pow_left₀ (by positivity) hbase 2
  have hpow : h ^ (5 * (d + 1)) ≤ h ^ (2 * (2 * d + 1)) :=
    pow_le_pow_of_le_one hh.le hh1 (by omega)
  calc
    _ ≤ (N * ((d : ℝ) + 1) * (K ^ ((d : ℝ) / 2) * C) / h ^ (2 * d + 1)) ^ 2 := hb.trans hsq
    _ = (N * ((d : ℝ) + 1) * (K ^ ((d : ℝ) / 2) * C)) ^ 2 / h ^ (2 * (2 * d + 1)) := by
      rw [div_pow, ← pow_mul, Nat.mul_comm (2 * d + 1) 2]
    _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hh _) hpow

/-- The source's `h^(-5n)` bound, with a constant independent of the scale,
the mode count, the coefficients, and the point. -/
theorem sourceRegularizedCurrent_crude_bound (d : ℕ) (N K C : ℝ)
    (hN : 0 ≤ N) (hK : 0 ≤ K) (hC0 : 0 ≤ C) :
    ∃ D : ℝ, 0 < D ∧ ∀ {ι : Type} [Fintype ι]
      (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
      (x : Index d → ℝ) (z : Index d → ℂ),
      0 < h → h ≤ 1 → h ≤ a → a ≤ ‖z none‖ →
      (∀ j, 0 < κ j) → (Fintype.card ι : ℝ) ≤ N / h ^ (d + 1) →
      (∀ j, κ j ≤ K / h) → (∀ j, ‖(⟨cR j, cI j⟩ : ℂ)‖ ≤ C) →
      (∀ j, (∑ i, |v j i| ^ 2) ≤ 1 / 1600) →
      fiberDefining (1 / 10) a z ≤ 0 →
      ‖sourceRegularizedCurrent h a κ cR cI v x z‖ ≤ D / h ^ (5 * (d + 1)) := by
  obtain ⟨B, hB, hcof⟩ := regularizingCofactor_norm_bound d
  let W := (N * ((d : ℝ) + 1) * (K ^ ((d : ℝ) / 2) * C)) ^ 2
  refine ⟨W + B, add_pos_of_nonneg_of_pos (sq_nonneg _) hB, ?_⟩
  intro ι inst h a κ cR cI v x z hh hh1 hha hay hκ hcount hfreq hC hv hr
  have hw := sourceWavePart_crude_bound h a N K C hh hh1 hN hK hC0
    κ cR cI v hκ x z (hha.trans hay) hcount hfreq hC hv hr
  have hc := hcof h a z hh hha hay hr
  have hp₁ : h ^ (48 * (d + 1)) ≤ 1 := pow_le_one₀ hh.le hh1
  have hp₂ : h ^ (5 * (d + 1)) ≤ 1 := pow_le_one₀ hh.le hh1
  have hc' : ‖h ^ (50 * (d + 1)) • fiberCofactor (1 / 10) a z‖ ≤ B / h ^ (5 * (d + 1)) := by
    apply hc.trans
    calc
      _ ≤ B := mul_le_of_le_one_right hB.le hp₁
      _ ≤ B / h ^ (5 * (d + 1)) := (le_div_iff₀ (pow_pos hh _)).mpr
        (mul_le_of_le_one_right hB.le hp₂)
  change ‖sourceWavePart h a κ cR cI v x z +
    h ^ (50 * (d + 1)) • fiberCofactor (1 / 10) a z‖ ≤ _
  exact (norm_add_le _ _).trans ((add_le_add hw hc').trans_eq (by simp [W, add_div]))

end OAI.Analysis.Calculus.Current
