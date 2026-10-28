import OAI.Analysis.Fourier.Restriction.Sparse.Input

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem localSmoothing_sparse_restriction_indexed (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (N : ℕ) (R : ℝ), 1 ≤ R →
      ∀ z : Fin N → Space n,
      (∀ i j, i ≠ j → R ^ (16 * n) * (N : ℝ) ^ (16 * n) ≤ dist (z i) (z j)) →
      ∀ f : Space n → ℂ, Measurable f → Integrable f →
      (∀ x, (∀ i, x ∉ ball (z i) R) → f x = 0) →
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal (restrictionInputExponent n)) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        C * ENNReal.ofReal (R ^ ε) * eLpNorm f (ENNReal.ofReal (restrictionInputExponent n)) volume := by
  obtain ⟨u, c, hc, hu, hr, hF, hFs⟩ := sparse_cutoff_exists n
  obtain ⟨hp, hp2⟩ := restrictionInputExponent_bounds hn
  let V := volume (closedBall (0 : Space n) 2)
  have hV : V ≠ ⊤ := (measure_closedBall_lt_top).ne
  obtain ⟨A, hA, HA⟩ := sparse_integralKernel_bound hn u hF hr hFs hp hp2 hV
  obtain ⟨B, hB, HB⟩ := localSmoothing_sparse_input_norm hls hn hε
  let t : ℝ := ((2 * Real.pi) ^ n)⁻¹
  have ht : 0 < t := by dsimp [t]; positivity
  let C := ENNReal.ofReal t * A * B * ENNReal.ofReal c⁻¹
  refine ⟨C, ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA) hB) ENNReal.ofReal_ne_top, ?_⟩
  intro N R hR z hsep f hfm hfi hfs
  let ν := volume.restrict (sphericalAnnulus (n := n) ((2 * R)⁻¹))
  have : IsFiniteMeasure ν := sparse_annulus_finite hR
  let g (i : Fin N) := sparsePiece u R (z i) f
  let G : Fin N × Space n → ℂ := fun p ↦ OAI.Analysis.Fourier.LocalSmoothing.angularFourier (g p.1) p.2
  let T := integralKernel (Measure.count.prod ν) (indexedLocalizedKernel u R z) G
  have hR0 : 0 < R := by linarith
  have hgi (i : Fin N) : Integrable (g i) := integrable_sparsePiece u hc hR0 hu (z i) hfm hfi
  have hGm : Measurable G := measurable_finite_fourier g hgi
  have hGi : Integrable G (Measure.count.prod ν) := integrable_finite_fourier g hgi ν
  have hd := sparse_balls_disjoint hn hR z hsep
  have Hop := HA N R hR z hsep ν inferInstance Measure.restrict_le_self
    (by simpa only [ν, Measure.restrict_apply_univ] using sparse_annulus_measure_le (n := n) hR) G hGm hGi
  have Hin := HB u c hc hu N R hR z hd f hfm hfi
  have heq : OAI.Analysis.Fourier.LocalSmoothing.angularFourier f =ᵐ[OAI.Analysis.Fourier.Restriction.sphereMeasure n] fun ω ↦ t • T ω := by
    filter_upwards [OAI.MeasureTheory.Kakeya.ae_sphereMeasure_norm n] with ω hω
    exact sparse_fourier_identity u hc hR hu hF hFs z hd hfm hfi hfs ω hω
  have hscale : ENNReal.ofReal R ^ (1 / restrictionInputExponent n) *
      ENNReal.ofReal ((2 * R)⁻¹) ^ (1 / restrictionInputExponent n) ≤ 1 := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ← ENNReal.ofReal_mul hR0.le, show R * (2 * R)⁻¹ = (1 / 2 : ℝ) by field_simp]
    simpa only [ENNReal.one_rpow] using ENNReal.rpow_le_rpow
      (by norm_num : ENNReal.ofReal (1 / 2 : ℝ) ≤ 1) (by positivity : 0 ≤ 1 / restrictionInputExponent n)
  rw [eLpNorm_congr_ae heq]
  change eLpNorm (t • T) (ENNReal.ofReal (restrictionInputExponent n)) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤ _
  rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs, abs_of_pos ht]
  calc
    _ ≤ ENNReal.ofReal t * (A * ENNReal.ofReal R ^ (1 / restrictionInputExponent n) *
        eLpNorm G (ENNReal.ofReal (restrictionInputExponent n)) (Measure.count.prod ν)) :=
      mul_le_mul' le_rfl Hop
    _ ≤ ENNReal.ofReal t * (A * ENNReal.ofReal R ^ (1 / restrictionInputExponent n) *
        (B * ENNReal.ofReal ((2 * R)⁻¹) ^ (1 / restrictionInputExponent n) * ENNReal.ofReal (R ^ ε) *
          ENNReal.ofReal c⁻¹ * eLpNorm f (ENNReal.ofReal (restrictionInputExponent n)) volume)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl Hin)
    _ = (C * ENNReal.ofReal (R ^ ε) * eLpNorm f (ENNReal.ofReal (restrictionInputExponent n)) volume) *
        (ENNReal.ofReal R ^ (1 / restrictionInputExponent n) *
          ENNReal.ofReal ((2 * R)⁻¹) ^ (1 / restrictionInputExponent n)) := by dsimp [C]; ring
    _ ≤ _ := by simpa only [mul_one] using mul_le_mul' le_rfl hscale

end OAI.Analysis.Fourier.Restriction
