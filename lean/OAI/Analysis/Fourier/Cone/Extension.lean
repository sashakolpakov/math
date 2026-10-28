import OAI.Analysis.Fourier.Cone.Diagonal
import OAI.Analysis.Fourier.Restriction.LocalSmoothing

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Cone

def coneFiniteExtension (n : ℕ) : FiniteExtension (coneMeasure n)
    (volume : Measure (Space n × ℝ)) where
  apply := coneExtension
  measurable _ hg := (continuous_coneExtension hg).measurable
  map_add f g hf hg z := by
    simp only [coneExtension, mul_add]
    exact integral_add (cone_integrand_integrable hf z) (cone_integrand_integrable hg z)
  map_const_mul c g z := by
    unfold coneExtension
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with η
    ring
  congr_ae h z := by
    apply integral_congr_ae
    filter_upwards [h] with η hη
    rw [hη]
  bound := enorm_coneExtension_le
  map_zero z := by simp [coneExtension]

theorem cone_diagonal_of_sphere_all {n : ℕ} {p : ℝ} (hp : 2 ≤ p) {C : ℝ≥0∞}
    (hC : C ≠ ⊤)
    (hsphere : ∀ f : Space n → ℂ, MemLp f (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) →
      eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension f) (ENNReal.ofReal p) volume ≤
        C * eLpNorm f (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n))
    {g : Space n × ℝ → ℂ} (hg : MemLp g (ENNReal.ofReal p) (coneMeasure n)) :
    eLpNorm (coneExtension g) (ENNReal.ofReal p) volume ≤
      (ENNReal.ofReal (2 * Real.pi) ^ (1 / p) * C *
        ENNReal.ofReal (Real.sqrt 2 * 2 ^ (n - 1))) * eLpNorm g (ENNReal.ofReal p) (coneMeasure n) := by
  let g' := hg.aestronglyMeasurable.mk g
  have he : g =ᵐ[coneMeasure n] g' := hg.aestronglyMeasurable.ae_eq_mk
  have hm : Measurable g' := hg.aestronglyMeasurable.measurable_mk
  have hp' : MemLp g' (ENNReal.ofReal p) (coneMeasure n) := hg.ae_eq he
  have H := cone_diagonal_of_sphere hp hC hsphere hm hp'
  have hE : coneExtension g = coneExtension g' :=
    funext ((coneFiniteExtension n).congr_ae he)
  rwa [← hE, ← eLpNorm_congr_ae he] at H

/-- Actual induced-surface extension estimates for the truncated forward
light cone, in the complete conjectured strict mixed range. -/
def ConeExtensionEstimates : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ a : ℝ≥0∞, 1 < a → ∀ b : ℝ,
    OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n < b →
    ((n : ℝ) + 1) / ((n : ℝ) - 1) * OAI.Analysis.Fourier.Restriction.conjugateExponent a < b →
    ∃ C : ℝ, 0 < C ∧ ∀ g : Space n × ℝ → ℂ, MemLp g a (coneMeasure n) →
      MemLp (coneExtension g) (ENNReal.ofReal b) ∧
      eLpNorm (coneExtension g) (ENNReal.ofReal b) volume ≤
        ENNReal.ofReal C * eLpNorm g a (coneMeasure n)

theorem sphericalRestriction_coneExtension (hsphere : OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture) :
    ConeExtensionEstimates := by
  intro n hn a ha b hb hab
  obtain ⟨s, hs, hsb, has⟩ := OAI.Analysis.Fourier.Restriction.exists_strict_diagonal_exponent
    (OAI.Analysis.Fourier.Restriction.conjugateExponent_pos ha) hb (by rwa [OAI.Analysis.Fourier.Restriction.criticalExponent_sub_one hn])
  have hs2 : 2 < s := (OAI.MeasureTheory.Kakeya.criticalExponent_gt_two hn).trans hs
  have hs1 : 1 < s := by linarith
  have hs0 : 0 < s := by linarith
  have has1 : (1 : ℝ≥0∞) < ENNReal.ofReal s := by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff hs0]
    exact hs1
  have hline : ((n : ℝ) + 1) / ((n : ℝ) - 1) *
      OAI.Analysis.Fourier.Restriction.conjugateExponent (ENNReal.ofReal s) < s := by
    rw [OAI.Analysis.Fourier.Restriction.conjugateExponent, ite_eq_right ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hs0.le]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by linarith : 0 < s - 1)).mpr
    have H : ((n : ℝ) + 1) / ((n : ℝ) - 1) < s - 1 := by
      rw [← OAI.Analysis.Fourier.Restriction.criticalExponent_sub_one hn]
      linarith
    nlinarith [mul_lt_mul_of_pos_right H hs0]
  obtain ⟨Cs, hCs, hS⟩ := hsphere n hn (ENNReal.ofReal s) has1 s hs hline
  let C : ℝ≥0∞ := ENNReal.ofReal (2 * Real.pi) ^ (1 / s) * ENNReal.ofReal Cs *
    ENNReal.ofReal (Real.sqrt 2 * 2 ^ (n - 1))
  have hCt : C ≠ ⊤ := by
    apply ENNReal.mul_ne_top _ ENNReal.ofReal_ne_top
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  have hd : ∀ g : Space n × ℝ → ℂ, MemLp g (ENNReal.ofReal s) (coneMeasure n) →
      eLpNorm ((coneFiniteExtension n) g) (ENNReal.ofReal s) volume ≤
        C * eLpNorm g (ENNReal.ofReal s) (coneMeasure n) := by
    intro g hg
    exact cone_diagonal_of_sphere_all hs2.le ENNReal.ofReal_ne_top (fun f hf => (hS f hf).2) hg
  obtain ⟨B, hBt, hB⟩ := OAI.Analysis.Fourier.Cone.FiniteExtension.mixed_diagonal
    (T := coneFiniteExtension n) ha hs1 hsb has hCt hd
  refine ⟨B.toReal + 1, by positivity, ?_⟩
  intro g hg
  have H := hB g hg
  have hBC : B ≤ ENNReal.ofReal (B.toReal + 1) := by
    rw [← ENNReal.ofReal_toReal hBt]
    exact ENNReal.ofReal_le_ofReal (by simp)
  exact ⟨H.trans_lt (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hBt) hg),
    H.trans (mul_le_mul' hBC le_rfl)⟩

/-- The cone corollary of Euclidean wave local smoothing. -/
theorem localSmoothing_coneExtension (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing) : ConeExtensionEstimates :=
  sphericalRestriction_coneExtension (OAI.Analysis.Fourier.Restriction.localSmoothing_sphericalRestrictionConjecture hls)

end OAI.Analysis.Fourier.Cone
