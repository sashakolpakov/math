import OAI.Analysis.Fourier.SquareFunction.Square.ExtensionRadius

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory FourierTransform Set
open scoped ENNReal
namespace OAI.Analysis.Fourier.SquareFunction

def steinSquareReal {n : ℕ} (α : ℝ) (f : SchwartzMap (Space n) ℂ) (x : Space n) : ℝ :=
  (OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f x).toReal

theorem measurable_steinSquareReal {n : ℕ} (α : ℝ) (f : SchwartzMap (Space n) ℂ) :
    Measurable (steinSquareReal α f) :=
  (measurable_steinSquareFunction α f).ennreal_toReal

theorem eLpNorm_steinSquareReal_le {n : ℕ} (α : ℝ) (f : SchwartzMap (Space n) ℂ)
    (p : ℝ≥0∞) :
    eLpNorm (steinSquareReal α f) p volume ≤
      eLpNorm (OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f) p volume := by
  apply eLpNorm_mono_enorm (measurable_steinSquareReal α f).aestronglyMeasurable
  intro x
  change ‖(OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f x).toReal‖ₑ ≤
    ‖OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f x‖ₑ
  rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg,enorm_eq_self]
  exact ENNReal.ofReal_toReal_le

theorem ae_steinSquareFunction_lt_top {n : ℕ} [NeZero n] {α : ℝ}
    (hα : 1 / 2 < α) (f : SchwartzMap (Space n) ℂ) :
    ∀ᵐ x ∂volume, OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f x < ⊤ := by
  have h := ae_lt_top ((measurable_steinSquareFunction α f).pow_const (2 : ℝ))
    (show (∫⁻ x, OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f x ^ (2 : ℝ)) ≠ ⊤ by
      rw [steinSquareFunction_integral_sq hα f]
      exact ENNReal.ofReal_ne_top)
  filter_upwards [h] with x hx
  apply lt_top_iff_ne_top.mpr
  intro he
  simp only [he,ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 2),lt_self_iff_false] at hx

theorem ae_enorm_steinSquareReal {n : ℕ} [NeZero n] {α : ℝ}
    (hα : 1 / 2 < α) (f : SchwartzMap (Space n) ℂ) :
    (fun x => ‖steinSquareReal α f x‖ₑ) =ᵐ[volume] OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f := by
  filter_upwards [ae_steinSquareFunction_lt_top hα f] with x hx
  simp only [steinSquareReal,Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hx.ne]

theorem abs_sub_toReal_eLpNorm_le {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f g : A → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |(eLpNorm f 2 μ).toReal - (eLpNorm g 2 μ).toReal| ≤
      (eLpNorm (f-g) 2 μ).toReal := by
  have h := abs_norm_sub_norm_le (hf.toLp f) (hg.toLp g)
  rw [← hf.toLp_sub hg,Lp.norm_toLp,Lp.norm_toLp,Lp.norm_toLp] at h
  exact h

/-- The reverse triangle inequality for the actual radius square function. -/
theorem ae_abs_steinSquareReal_sub_le {n : ℕ} [NeZero n] {α : ℝ}
    (hα : 1 / 2 < α) (f g : SchwartzMap (Space n) ℂ) :
    ∀ᵐ x ∂volume, |steinSquareReal α f x - steinSquareReal α g x| ≤
      steinSquareReal α (f-g) x := by
  filter_upwards [ae_steinSquareFunction_lt_top hα f,
    ae_steinSquareFunction_lt_top hα g] with x hfx hgx
  have hf : MemLp (fun r => radiusDerivativeCycles α r f x) 2 squareRadiusMeasure := by
    change eLpNorm _ _ _ < ⊤
    rwa [← steinSquareFunction_eq_radius_eLpNorm]
  have hg : MemLp (fun r => radiusDerivativeCycles α r g x) 2 squareRadiusMeasure := by
    change eLpNorm _ _ _ < ⊤
    rwa [← steinSquareFunction_eq_radius_eLpNorm]
  have he := eLpNorm_congr_ae (p := (2 : ℝ≥0∞)) (ae_radiusDerivativeCycles_sub hα f g x)
  have h := abs_sub_toReal_eLpNorm_le hf hg
  change |(eLpNorm (fun r => radiusDerivativeCycles α r f x) 2 squareRadiusMeasure).toReal -
      (eLpNorm (fun r => radiusDerivativeCycles α r g x) 2 squareRadiusMeasure).toReal| ≤
    (eLpNorm (fun r => radiusDerivativeCycles α r f x - radiusDerivativeCycles α r g x)
      2 squareRadiusMeasure).toReal at h
  rw [← he,← steinSquareFunction_eq_radius_eLpNorm,
    ← steinSquareFunction_eq_radius_eLpNorm,← steinSquareFunction_eq_radius_eLpNorm] at h
  exact h

theorem eLpNorm_steinSquareReal_sub_le {n : ℕ} [NeZero n] {α : ℝ}
    (hα : 1 / 2 < α) (f g : SchwartzMap (Space n) ℂ) (p : ℝ≥0∞) :
    eLpNorm (steinSquareReal α f - steinSquareReal α g) p volume ≤
      eLpNorm (OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α (f-g)) p volume := by
  apply (eLpNorm_mono_ae ((measurable_steinSquareReal α f).sub
    (measurable_steinSquareReal α g)).aestronglyMeasurable ?_).trans
      (eLpNorm_steinSquareReal_le α (f-g) p)
  filter_upwards [ae_abs_steinSquareReal_sub_le hα f g] with x hx
  simpa only [Pi.sub_apply,Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ steinSquareReal α (f-g) x from ENNReal.toReal_nonneg)] using hx

end OAI.Analysis.Fourier.SquareFunction
