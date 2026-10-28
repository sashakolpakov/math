import OAI.Geometry.Nikodym.FullStripMoment

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped ENNReal
namespace OAI.Geometry.Nikodym


theorem ennreal_le_of_nat_pow_le {a b : ℝ≥0∞} {n : ℕ} (hn : 0 < n)
    (h : a^n ≤ b^n) : a ≤ b := by
  apply (ENNReal.rpow_le_rpow_iff (show (0:ℝ)<n by exact_mod_cast hn)).mp
  simpa only [ENNReal.rpow_natCast] using h

theorem fullStrip_lp_bound_ennreal (hK : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture)
    {d : ℕ} (hd : 1 ≤ d) {V ε : ℝ} (hV : 0 ≤ V) (hε : 0 < ε) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 → stripDilation V*δ ≤ 1 →
      ∀ f : Space (d+1) → ℂ, Measurable f → MemLp f (d+1 : ℕ) volume →
        eLpNorm (fullStrip δ V f) (d+1 : ℕ) volume ≤
          C * ENNReal.ofReal (δ^(-ε)) * eLpNorm f (d+1 : ℕ) volume := by
  obtain ⟨C,hC,h⟩ := fullStrip_moment_bound hK hd hV hε
  let R := C^((d+1:ℝ)⁻¹)
  have hR : R < ⊤ := by dsimp [R]; finiteness
  have hRn : R^(d+1) = C := by
    dsimp only [R]
    rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
    rw [Nat.cast_add,Nat.cast_one,inv_mul_cancel₀ (by positivity),ENNReal.rpow_one]
  refine ⟨R,hR,?_⟩
  intro δ hδ hh hD f hf hfp
  apply ennreal_le_of_nat_pow_le (n:=d+1) (by omega)
  rw [mul_pow,mul_pow,hRn,
    eLpNorm_nat_pow_eq_lintegral (by omega) (measurable_fullStrip δ V hf).aestronglyMeasurable,
    eLpNorm_nat_pow_eq_lintegral (by omega) hf.aestronglyMeasurable]
  simpa using h δ hδ hh hD f hf hfp

theorem fullStrip_lp_bound (hK : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture)
    {d : ℕ} (hd : 1 ≤ d) {V ε : ℝ} (hV : 0 ≤ V) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 → stripDilation V*δ ≤ 1 →
      ∀ f : Space (d+1) → ℂ, Measurable f → MemLp f (d+1 : ℕ) volume →
        eLpNorm (fullStrip δ V f) (d+1 : ℕ) volume ≤
          ENNReal.ofReal (C*δ^(-ε)) * eLpNorm f (d+1 : ℕ) volume := by
  obtain ⟨C,hC,h⟩ := fullStrip_lp_bound_ennreal hK hd hV hε
  refine ⟨C.toReal+1,by positivity,?_⟩
  intro δ hδ hh hD f hf hfp
  apply (h δ hδ hh hD f hf hfp).trans
  apply mul_le_mul' _ le_rfl
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ C.toReal+1)]
  apply mul_le_mul' _ le_rfl
  calc
    C = ENNReal.ofReal C.toReal := (ENNReal.ofReal_toReal hC.ne).symm
    _ ≤ ENNReal.ofReal (C.toReal+1) := ENNReal.ofReal_le_ofReal (by linarith)

end OAI.Geometry.Nikodym
