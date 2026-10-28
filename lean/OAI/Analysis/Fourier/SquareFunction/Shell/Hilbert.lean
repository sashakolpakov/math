import OAI.Analysis.Fourier.SquareFunction.Radius.Hilbert
import OAI.Analysis.Fourier.SquareFunction.Shell.Continuity

open OAI.Analysis.Fourier.Wave

/-! The actual thin-shell operator with values in `L²([1,2])`. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform
open scoped ENNReal ContDiff

noncomputable def radiusCurry {X : Type*} [TopologicalSpace X]
    (F : X × ℝ → ℂ) (hF : Continuous F) (x : X) : C(RadiusInterval, ℂ) :=
  ⟨fun r => F (x, r), hF.comp (continuous_const.prodMk continuous_subtype_val)⟩

theorem continuous_radiusCurry {X : Type*} [TopologicalSpace X]
    (F : X × ℝ → ℂ) (hF : Continuous F) : Continuous (radiusCurry F hF) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : X × RadiusInterval => F (z.1, (z.2 : ℝ)))
  exact hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

noncomputable def thinShellRadiusMap {n : ℕ} (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) : Space n → C(RadiusInterval, ℂ) :=
  radiusCurry (fun z => thinShellCycles φ δ f z.1 z.2) (continuous_thinShellCycles_joint φ δ f)

theorem continuous_thinShellRadiusMap {n : ℕ} (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) : Continuous (thinShellRadiusMap φ δ f) :=
  continuous_radiusCurry _ _

noncomputable def thinShellHilbert {n : ℕ} (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) : RadiusHilbert :=
  radiusToL2 (thinShellRadiusMap φ δ f x)

theorem continuous_thinShellHilbert {n : ℕ} (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) : Continuous (thinShellHilbert φ δ f) :=
  radiusToL2.continuous.comp (continuous_thinShellRadiusMap φ δ f)

theorem thinShellHilbert_coe {n : ℕ} (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    (thinShellHilbert φ δ f x : RadiusInterval → ℂ) =ᵐ[radiusMeasure]
      (fun r => thinShellCycles φ δ f x r) := radiusToL2_coe _

theorem enorm_thinShellHilbert {n : ℕ} (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    ‖thinShellHilbert φ δ f x‖ₑ =
      eLpNorm (thinShellCycles φ δ f x) 2 (volume.restrict (Set.Icc (1 : ℝ) 2)) := by
  rw [thinShellHilbert, enorm_radiusToL2]
  change eLpNorm (fun r : RadiusInterval => thinShellCycles φ δ f x r) 2 radiusMeasure = _
  exact eLpNorm_radius_restriction (thinShellCycles φ δ f x) 2

theorem norm_thinShellHilbert_le_squareNorm {n : ℕ} (φ : SchwartzMap ℝ ℂ)
    {δ : ℝ} (hδ : 0 < δ) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    ‖thinShellHilbert φ δ f x‖ ≤ ‖thinShellSquareNorm φ δ f x‖ := by
  apply (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).mp
  rw [ofReal_norm, ofReal_norm, enorm_thinShellSquareNorm φ hδ f x,
    enorm_thinShellHilbert]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

theorem eLpNorm_thinShellHilbert_le_squareNorm {n : ℕ} (φ : SchwartzMap ℝ ℂ)
    {δ : ℝ} (hδ : 0 < δ) (f : SchwartzMap (Space n) ℂ) (p : ℝ≥0∞) :
    eLpNorm (thinShellHilbert φ δ f) p volume ≤
      eLpNorm (thinShellSquareNorm φ δ f) p volume := by
  apply eLpNorm_mono (continuous_thinShellHilbert φ δ f).aestronglyMeasurable
  exact norm_thinShellHilbert_le_squareNorm φ hδ f

theorem thinShellHilbert_two_bound {n : ℕ} (φ : SchwartzMap ℝ ℂ)
    {δ : ℝ} (hδ : 0 < δ) (f : SchwartzMap (Space n) ℂ) :
    eLpNorm (thinShellHilbert φ δ f) 2 volume ≤
      ENNReal.ofReal δ ^ (1 / 2 : ℝ) * eLpNorm φ 2 volume * eLpNorm f 2 volume := by
  exact (eLpNorm_thinShellHilbert_le_squareNorm φ hδ f 2).trans_eq
    (eLpNorm_thinShellSquareNorm_two φ hδ f)

theorem localSmoothing_projected_thinShellHilbert (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {χ ψ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hzero : (0 : Space n) ∉ tsupport ψ) (hcut : ∀ ξ, χ ξ ≠ 0 → ψ ξ = 1)
    (φ : SchwartzMap ℝ ℂ) {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (thinShellHilbert φ δ (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ 1 f))
        (ENNReal.ofReal p) volume ≤
        (C * ENNReal.ofReal (δ ^ (1 / 2 - (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε)))) *
          eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hbound⟩ := localSmoothing_projected_thinShell_mixed hls hn hχ hcχ hψ hcψ
    hzero hcut φ hp hε
  refine ⟨C, hC, fun δ hδ hδone f => ?_⟩
  exact (eLpNorm_thinShellHilbert_le_squareNorm φ hδ _ _).trans (hbound δ hδ hδone f).2

end OAI.Analysis.Fourier.SquareFunction
