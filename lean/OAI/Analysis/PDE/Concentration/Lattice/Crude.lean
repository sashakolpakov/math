import OAI.Analysis.PDE.Concentration.Lattice.Flux
import OAI.Analysis.Calculus.Current.Crude

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion
open scoped Matrix Matrix.Norms.Elementwise

theorem latticeWavePart_norm_le {d : ℕ} {ι : Type*} [Fintype ι]
    (L : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (h a R C : ℝ) (hh : 0 < h) (hR0 : 0 ≤ R) (hC0 : 0 ≤ C)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (hκ : ∀ j, 0 < κ j)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) (hY : z none ≠ 0)
    (hR : ∀ j, κ j / ‖z none‖ ≤ R) (hC : ∀ j, ‖(⟨cR j, cI j⟩ : ℂ)‖ ≤ C)
    (hv : ∀ j, (∑ i, |v j i| ^ 2) ≤ 1 / 1600)
    (hr : OAI.Analysis.Calculus.Current.fiberDefining (1 / 10) a z ≤ 0) :
    ‖latticeWavePart L h a κ cR cI v x z‖ ≤ ((Fintype.card ι : ℝ) * ((d : ℝ) + 1) *
      (R ^ ((d : ℝ) / 2) * C)) ^ 2 := by
  let := latticeKernelMeasure_isProbability L h hh
  apply (OAI.Analysis.Calculus.Current.cutoffCurrent_norm_le a _ x z).trans
  have hpoint (t : OAI.Analysis.Calculus.Current.SpatialCube d) := OAI.Analysis.Calculus.Current.waveCurrent_norm_le_parameters
    κ cR cI v R C 0 hκ hR0 hC0 (x + latticeCubeShift L t) z hY hR hC
    (fun j i => OAI.Analysis.Calculus.Current.velocity_coordinate_le_one (v j) (hv j) i)
    (OAI.Analysis.Calculus.Current.fiber_ratio_coordinate_le_one a z hr)
    (fun j => mul_nonneg (div_nonneg (mul_nonneg (hκ j).le (norm_nonneg _)) (by norm_num))
      (Finset.sum_nonneg fun i _ => sq_nonneg _))
  have hn := norm_integral_le_of_norm_le_const (μ := latticeKernelMeasure L h)
    (Filter.Eventually.of_forall hpoint)
  simpa [latticeWavePart, OAI.Analysis.Calculus.Current.averagedWaveCurrent, measureReal_def] using! hn

theorem latticeWavePart_crude_bound {d : ℕ} {ι : Type*} [Fintype ι]
    (L : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (h a N K C : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (_ : 0 ≤ N) (hK : 0 ≤ K) (hC0 : 0 ≤ C)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (hκ : ∀ j, 0 < κ j)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) (hy : h ≤ ‖z none‖)
    (hcount : (Fintype.card ι : ℝ) ≤ N / h ^ (d + 1))
    (hfreq : ∀ j, κ j ≤ K / h) (hC : ∀ j, ‖(⟨cR j, cI j⟩ : ℂ)‖ ≤ C)
    (hv : ∀ j, (∑ i, |v j i| ^ 2) ≤ 1 / 1600)
    (hr : OAI.Analysis.Calculus.Current.fiberDefining (1 / 10) a z ≤ 0) :
    ‖latticeWavePart L h a κ cR cI v x z‖ ≤
      (N * ((d : ℝ) + 1) * (K ^ ((d : ℝ) / 2) * C)) ^ 2 / h ^ (5 * (d + 1)) := by
  have hY : z none ≠ 0 := norm_pos_iff.mp (hh.trans_le hy)
  have hb := latticeWavePart_norm_le L h a (K / h ^ 2) C hh (by positivity) hC0
    κ cR cI v hκ x z hY (fun j => OAI.Analysis.Calculus.Current.frequency_over_height_bound h K (κ j) _ hh
      (hκ j).le (hfreq j) hy) hC hv hr
  rw [OAI.Analysis.Calculus.Current.scale_rpow_half h K d hh hK] at hb
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

/-- The manuscript's crude current bound is uniform over arbitrary full
spatial lattice charts, not just the axis-aligned torus. -/
theorem latticeRegularizedCurrent_crude_bound (d : ℕ) (N K C : ℝ)
    (hN : 0 ≤ N) (hK : 0 ≤ K) (hC0 : 0 ≤ C) :
    ∃ D : ℝ, 0 < D ∧ ∀ (L : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) {ι : Type} [Fintype ι]
      (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
      (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ),
      0 < h → h ≤ 1 → h ≤ a → a ≤ ‖z none‖ →
      (∀ j, 0 < κ j) → (Fintype.card ι : ℝ) ≤ N / h ^ (d + 1) →
      (∀ j, κ j ≤ K / h) → (∀ j, ‖(⟨cR j, cI j⟩ : ℂ)‖ ≤ C) →
      (∀ j, (∑ i, |v j i| ^ 2) ≤ 1 / 1600) →
      OAI.Analysis.Calculus.Current.fiberDefining (1 / 10) a z ≤ 0 →
      ‖latticeRegularizedCurrent L h a κ cR cI v x z‖ ≤ D / h ^ (5 * (d + 1)) := by
  obtain ⟨B, hB, hcof⟩ := OAI.Analysis.Calculus.Current.regularizingCofactor_norm_bound d
  let W := (N * ((d : ℝ) + 1) * (K ^ ((d : ℝ) / 2) * C)) ^ 2
  refine ⟨W + B, add_pos_of_nonneg_of_pos (sq_nonneg _) hB, ?_⟩
  intro L ι inst h a κ cR cI v x z hh hh1 hha hay hκ hcount hfreq hC hv hr
  have hw := latticeWavePart_crude_bound L h a N K C hh hh1 hN hK hC0
    κ cR cI v hκ x z (hha.trans hay) hcount hfreq hC hv hr
  have hc := hcof h a z hh hha hay hr
  have hp₁ : h ^ (48 * (d + 1)) ≤ 1 := pow_le_one₀ hh.le hh1
  have hp₂ : h ^ (5 * (d + 1)) ≤ 1 := pow_le_one₀ hh.le hh1
  have hc' : ‖h ^ (50 * (d + 1)) • OAI.Analysis.Calculus.Current.fiberCofactor (1 / 10) a z‖ ≤ B / h ^ (5 * (d + 1)) := by
    apply hc.trans
    calc
      _ ≤ B := mul_le_of_le_one_right hB.le hp₁
      _ ≤ B / h ^ (5 * (d + 1)) := (le_div_iff₀ (pow_pos hh _)).mpr
        (mul_le_of_le_one_right hB.le hp₂)
  change ‖latticeWavePart L h a κ cR cI v x z +
    h ^ (50 * (d + 1)) • OAI.Analysis.Calculus.Current.fiberCofactor (1 / 10) a z‖ ≤ _
  exact (norm_add_le _ _).trans ((add_le_add hw hc').trans_eq (by simp [W, add_div]))

end OAI.Analysis.PDE.Concentration
