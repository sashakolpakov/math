import OAI.Analysis.Fourier.BochnerRiesz.CompactFamily

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz


theorem enorm_continuousMap_le {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (u : C(X, ℂ)) {B : ℝ≥0∞} (hb : ∀ x, ‖u x‖ₑ ≤ B) : ‖u‖ₑ ≤ B := by
  by_cases hB : B = ∞
  · simp [hB]
  have hu : ‖u‖ ≤ B.toReal := by
    apply (ContinuousMap.norm_le u ENNReal.toReal_nonneg).mpr
    intro x
    have h := ENNReal.toReal_mono hB (hb x)
    simpa using h
  have h := ENNReal.ofReal_le_ofReal hu
  simpa only [ofReal_norm, ENNReal.ofReal_toReal hB] using h

theorem enorm_brCompactFamily_le {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    ‖brCompactFamily hδ f x‖ₑ ≤ OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszMaximal δ f x + ‖f x‖ₑ := by
  apply enorm_continuousMap_le
  intro τ
  by_cases hτ : (τ : ℝ) = 0
  · have ht : τ = inverseRadiusZero := Subtype.ext hτ
    rw [ht, brCompactFamily_zero]
    exact le_add_self
  · have ht : 0 < (τ : ℝ) := lt_of_le_of_ne τ.property.1 (Ne.symm hτ)
    rw [brCompactFamily_pos hδ f x τ ht]
    apply le_trans _ le_self_add
    exact le_iSup_of_le (τ : ℝ)⁻¹ (le_iSup_of_le (inv_pos.mpr ht) le_rfl)

theorem eLpNorm_brCompactFamily_le {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (f : SchwartzMap (Space n) ℂ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (brCompactFamily hδ f) p volume ≤
      eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszMaximal δ f) p volume + eLpNorm f p volume := by
  calc
    _ ≤ eLpNorm (fun x => OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszMaximal δ f x + ‖f x‖ₑ) p volume := by
      apply eLpNorm_mono_enorm (continuous_brCompactFamily hδ f).aestronglyMeasurable
      intro x
      simpa only [enorm_eq_self] using enorm_brCompactFamily_le hδ f x
    _ ≤ eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszMaximal δ f) p volume +
        eLpNorm (fun x => ‖f x‖ₑ) p volume := eLpNorm_add_le hp
    _ = _ := by rw [eLpNorm_enorm _ f.continuous.aestronglyMeasurable]

theorem localSmoothing_brCompactFamily_bound (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {p δ : ℝ} (hp : 2 ≤ p)
    (hδ : OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (brCompactFamily ((le_max_left _ _).trans hδ.le) f) (ENNReal.ofReal p) volume ∧
      eLpNorm (brCompactFamily ((le_max_left _ _).trans hδ.le) f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hb⟩ := OAI.Analysis.Fourier.SquareFunction.localSmoothing_maximalBochnerRiesz hls hn hp hδ
  refine ⟨C + 1, by linarith, fun f => ?_⟩
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
  have H := (eLpNorm_brCompactFamily_le ((le_max_left _ _).trans hδ.le) f hp1).trans
    (add_le_add (hb f).2 le_rfl)
  have he : ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume +
      eLpNorm f (ENNReal.ofReal p) volume =
      ENNReal.ofReal (C + 1) * eLpNorm f (ENNReal.ofReal p) volume := by
    rw [ENNReal.ofReal_add hC.le (by norm_num), ENNReal.ofReal_one, add_mul, one_mul]
  rw [he] at H
  exact ⟨H.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (f.memLp _ volume)), H⟩

end OAI.Analysis.Fourier.BochnerRiesz
