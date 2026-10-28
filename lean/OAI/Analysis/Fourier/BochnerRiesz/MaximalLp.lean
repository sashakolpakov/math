import OAI.Analysis.Fourier.BochnerRiesz.BoundedExtension

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz


theorem enorm_bcf_eq_iSup {X : Type*} [TopologicalSpace X]
    (F : BoundedContinuousFunction X ℂ) : ‖F‖ₑ = ⨆ x, ‖F x‖ₑ := by
  apply le_antisymm
  · exact enorm_boundedContinuousFunction_le F (fun x => le_iSup (fun x => ‖F x‖ₑ) x)
  · exact iSup_le fun x => by simpa only [ofReal_norm] using
      ENNReal.ofReal_le_ofReal (F.norm_coe_le_norm x)

def brFullRepresentative {n : ℕ} {p : ℝ≥0∞} (F : BrBoundedLp n p)
    (R : ℝ) (x : Space n) : ℂ := if h : 0 < R then F x ⟨R, h⟩ else 0

def brFullMaximal {n : ℕ} {p : ℝ≥0∞} (F : BrBoundedLp n p) (x : Space n) : ℝ≥0∞ :=
  ⨆ R : ℝ, ⨆ (_ : 0 < R), ‖brFullRepresentative F R x‖ₑ

theorem brFullMaximal_eq_enorm {n : ℕ} {p : ℝ≥0∞} (F : BrBoundedLp n p) (x : Space n) :
    brFullMaximal F x = ‖F x‖ₑ := by
  rw [enorm_bcf_eq_iSup]
  apply le_antisymm
  · apply iSup_le
    intro R
    apply iSup_le
    intro hR
    simp only [brFullRepresentative, dite_eq_left hR]
    exact le_iSup (fun R : PositiveRadius => ‖F x R‖ₑ) ⟨R, hR⟩
  · apply iSup_le
    intro R
    apply le_iSup_of_le R.val
    apply le_iSup_of_le R.property
    have hR : 0 < (R : ℝ) := R.property
    simp only [brFullRepresentative, dite_eq_left hR]
    have he : (⟨(R : ℝ), hR⟩ : PositiveRadius) = R := Subtype.ext rfl
    rw [he]

theorem measurable_brFullMaximal {n : ℕ} {p : ℝ≥0∞} (F : BrBoundedLp n p) :
    Measurable (brFullMaximal F) := by
  rw [show brFullMaximal F = (fun x => ‖F x‖ₑ) from funext (brFullMaximal_eq_enorm F)]
  exact (continuous_enorm.comp_stronglyMeasurable (Lp.stronglyMeasurable F)).measurable

theorem eLpNorm_brFullMaximal {n : ℕ} {p : ℝ≥0∞} (F : BrBoundedLp n p) :
    eLpNorm (brFullMaximal F) p volume = ‖F‖ₑ := by
  rw [show brFullMaximal F = (fun x => ‖F x‖ₑ) from funext (brFullMaximal_eq_enorm F)]
  rw [eLpNorm_enorm _ (Lp.aestronglyMeasurable F), Lp.enorm_def]

/-- The maximal estimate on the whole `Lᵖ` space, for a single joint
representative continuous in every positive radius. -/
theorem localSmoothing_bochnerRiesz_Lp_full_maximal (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {p δ : ℝ} (hp : 2 ≤ p)
    [Fact (1 ≤ ENNReal.ofReal p)] (hδ : OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ U : BrLp n (ENNReal.ofReal p) →L[ℂ] BrBoundedLp n (ENNReal.ofReal p),
      ‖U‖ ≤ C ∧
      (∀ f : SchwartzMap (Space n) ℂ, ∀ᵐ x ∂volume, ∀ R : ℝ, 0 < R →
        brFullRepresentative (U (f.toLp (ENNReal.ofReal p) volume)) R x = OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x) ∧
      (∀ f : BrLp n (ENNReal.ofReal p),
        Measurable (brFullMaximal (U f)) ∧
        eLpNorm (brFullMaximal (U f)) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal C * ‖f‖ₑ) := by
  obtain ⟨C, hC, U, hUnorm, hUs⟩ := localSmoothing_brBoundedLp_operator hls hn hp hδ
  refine ⟨C, hC, U, hUnorm, ?_, ?_⟩
  · intro f
    filter_upwards [hUs f] with x hx
    intro R hR
    simp only [brFullRepresentative, dite_eq_left hR, hx]
    rfl
  · intro f
    refine ⟨measurable_brFullMaximal _, ?_⟩
    rw [eLpNorm_brFullMaximal]
    have H := ENNReal.ofReal_le_ofReal
      ((U.le_opNorm f).trans (mul_le_mul_of_nonneg_right hUnorm (norm_nonneg _)))
    simpa only [ENNReal.ofReal_mul hC.le, ofReal_norm] using H

end OAI.Analysis.Fourier.BochnerRiesz
