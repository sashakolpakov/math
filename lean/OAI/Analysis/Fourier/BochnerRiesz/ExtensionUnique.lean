import OAI.Analysis.Fourier.BochnerRiesz.FullSummability

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

/-- Bounded finite-`p` extensions are determined by their actual Schwartz
values; in particular they do not depend on an approximation sequence. -/
theorem bochnerRiesz_Lp_extension_unique {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hpt : p ≠ ⊤) {δ R : ℝ} (T U : BrLp n p →L[ℂ] BrLp n p)
    (hT : ∀ f : SchwartzMap (Space n) ℂ,
      (T (f.toLp p volume) : Space n → ℂ) =ᵐ[volume] OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f)
    (hU : ∀ f : SchwartzMap (Space n) ℂ,
      (U (f.toLp p volume) : Space n → ℂ) =ᵐ[volume] OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) : T = U := by
  have hd : DenseRange (fun f : SchwartzMap (Space n) ℂ => f.toLp p volume) :=
    SchwartzMap.denseRange_toLpCLM hpt
  have hb (f : SchwartzMap (Space n) ℂ) : T (f.toLp p volume) = U (f.toLp p volume) :=
    Lp.ext ((hT f).trans (hU f).symm)
  have he : (fun f => T f) = (fun f => U f) := hd.equalizer T.continuous U.continuous (funext hb)
  apply ContinuousLinearMap.ext
  intro f
  exact congrFun he f

/-- Evaluating the coherent maximal representative gives precisely any
bounded scalar multiplier extension with the same Schwartz values. -/
theorem brFullEval_eq_extension {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hpt : p ≠ ⊤) {δ R : ℝ} (hR : 0 < R)
    (W : BrLp n p →L[ℂ] BrBoundedLp n p) (T : BrLp n p →L[ℂ] BrLp n p)
    (hW : ∀ f : SchwartzMap (Space n) ℂ, ∀ᵐ x ∂volume, ∀ S : ℝ, 0 < S →
      brFullRepresentative (W (f.toLp p volume)) S x = OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ S f x)
    (hT : ∀ f : SchwartzMap (Space n) ℂ,
      (T (f.toLp p volume) : Space n → ℂ) =ᵐ[volume] OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) :
    (brFullEval R).comp W = T := by
  apply bochnerRiesz_Lp_extension_unique hpt _ T _ hT
  intro f
  filter_upwards [brFullEval_coe R (W (f.toLp p volume)), hW f] with x hx hw
  exact hx.trans (hw R hR)

end OAI.Analysis.Fourier.BochnerRiesz
