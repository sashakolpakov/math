import OAI.Analysis.Fourier.Radial.BRConjecture
import Mathlib.Analysis.Normed.Operator.Extend

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz


abbrev BrLp (n : ℕ) (p : ℝ≥0∞) := Lp (α := Space n) ℂ p volume

theorem bochnerRiesz_schwartz_add {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (R : ℝ)
    (f g : SchwartzMap (Space n) ℂ) :
    OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R (f + g) = OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f + OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R g := by
  simp only [bochnerRiesz_eq_fourierInv, ← SchwartzMap.fourier_coe]
  change (𝓕⁻ (fun ξ => bochnerRieszCyclesSymbol δ R ξ *
    (𝓕 (f + g) : SchwartzMap (Space n) ℂ) ξ)) = _
  rw [FourierTransform.fourier_add]
  simp only [add_apply, mul_add]
  exact fourierInv_add_integrable
    (integrable_bochnerRieszSymbol_mul hδ R _ (𝓕 f).integrable)
    (integrable_bochnerRieszSymbol_mul hδ R _ (𝓕 g).integrable)

theorem bochnerRiesz_schwartz_smul {n : ℕ} (δ R : ℝ) (c : ℂ)
    (f : SchwartzMap (Space n) ℂ) :
    OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R (c • f) = c • OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f := by
  simp only [bochnerRiesz_eq_fourierInv, ← SchwartzMap.fourier_coe, fourier_smul,
    smul_apply, smul_eq_mul]
  have he : (fun ξ : Space n => bochnerRieszCyclesSymbol δ R ξ * (c * (𝓕 f) ξ)) =
      fun ξ => c * (bochnerRieszCyclesSymbol δ R ξ * (𝓕 f) ξ) := by
    funext ξ
    ring
  rw [he, fourierInv_const_mul]
  rfl

def bochnerRieszSchwartzToLp {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {δ : ℝ} (hδ : 0 ≤ δ) (R : ℝ)
    (hLp : ∀ f : SchwartzMap (Space n) ℂ, MemLp (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) p volume) :
    SchwartzMap (Space n) ℂ →ₗ[ℂ] BrLp n p where
  toFun f := (hLp f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(hLp (f + g)).coeFn_toLp, (hLp f).coeFn_toLp, (hLp g).coeFn_toLp,
      Lp.coeFn_add ((hLp f).toLp _) ((hLp g).toLp _)] with x hfg hf hg hs
    rw [hfg, hs, Pi.add_apply, hf, hg]
    exact congrFun (bochnerRiesz_schwartz_add hδ R f g) x
  map_smul' c f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [(hLp (c • f)).coeFn_toLp, (hLp f).coeFn_toLp,
      Lp.coeFn_smul c ((hLp f).toLp _)] with x hcf hf hs
    rw [hcf, hs, Pi.smul_apply, hf]
    exact congrFun (bochnerRiesz_schwartz_smul δ R c f) x

def bochnerRieszLpExtend {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {δ : ℝ} (hδ : 0 ≤ δ) (R : ℝ)
    (hLp : ∀ f : SchwartzMap (Space n) ℂ, MemLp (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) p volume) :
    BrLp n p →L[ℂ] BrLp n p :=
  (bochnerRieszSchwartzToLp hδ R hLp).extendOfNorm
    (SchwartzMap.toLpCLM ℂ ℂ p volume).toLinearMap

theorem norm_bochnerRieszSchwartzToLp_le {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {δ : ℝ} (hδ : 0 ≤ δ) (R : ℝ)
    (hLp : ∀ f : SchwartzMap (Space n) ℂ, MemLp (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) p volume)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ f : SchwartzMap (Space n) ℂ, eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) p volume ≤
      ENNReal.ofReal C * eLpNorm f p volume) (f : SchwartzMap (Space n) ℂ) :
    ‖bochnerRieszSchwartzToLp hδ R hLp f‖ ≤ C * ‖f.toLp p volume‖ := by
  change ‖(hLp f).toLp _‖ ≤ _
  rw [Lp.norm_toLp, SchwartzMap.norm_toLp]
  have H := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (f.memLp p volume).ne) (hb f)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using H

theorem bochnerRieszLpExtend_properties {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hpt : p ≠ ⊤) {δ : ℝ} (hδ : 0 ≤ δ) (R : ℝ)
    (hLp : ∀ f : SchwartzMap (Space n) ℂ, MemLp (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) p volume)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ f : SchwartzMap (Space n) ℂ, eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) p volume ≤
      ENNReal.ofReal C * eLpNorm f p volume) :
    ‖bochnerRieszLpExtend hδ R hLp‖ ≤ C ∧
      ∀ f : SchwartzMap (Space n) ℂ,
        bochnerRieszLpExtend hδ R hLp (f.toLp p volume) = (hLp f).toLp _ := by
  have hd : DenseRange (SchwartzMap.toLpCLM ℂ ℂ p (volume : Measure (Space n))).toLinearMap :=
    SchwartzMap.denseRange_toLpCLM hpt
  have hnorm := norm_bochnerRieszSchwartzToLp_le hδ R hLp hC hb
  exact ⟨LinearMap.opNorm_extendOfNorm_le hd hC hnorm,
    fun f => LinearMap.extendOfNorm_eq hd ⟨C, hnorm⟩ f⟩

/-- Full finite-`p` bounded linear realizations of Bochner--Riesz, agreeing
almost everywhere with the Fourier integral on Schwartz functions. -/
theorem localSmoothing_bochnerRiesz_Lp_operators (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpt : p ≠ ⊤)
    {δ : ℝ} (hδ : OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex n p < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : Set.Ioi (0 : ℝ) → (BrLp n p →L[ℂ] BrLp n p),
      (∀ R, ‖T R‖ ≤ C) ∧ ∀ R (f : SchwartzMap (Space n) ℂ),
        (T R (f.toLp p volume) : Space n → ℂ) =ᵐ[volume] OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R.val f := by
  have hp : 1 ≤ p := Fact.out
  have hδ0 : 0 ≤ δ := (le_max_right _ _).trans hδ.le
  obtain ⟨C, hC, hbound⟩ := OAI.Analysis.Fourier.Radial.localSmoothing_bochnerRieszConjecture hls n hn p hp δ hδ
  let hLp (R : Set.Ioi (0 : ℝ)) (f : SchwartzMap (Space n) ℂ) := (hbound R.val R.property f).1
  let T (R : Set.Ioi (0 : ℝ)) := bochnerRieszLpExtend hδ0 R.val (hLp R)
  have ht (R : Set.Ioi (0 : ℝ)) := bochnerRieszLpExtend_properties hpt hδ0 R.val (hLp R)
    hC.le (fun f => (hbound R.val R.property f).2)
  refine ⟨C, hC, T, fun R => (ht R).1, ?_⟩
  intro R f
  rw [(ht R).2 f]
  exact (hLp R f).coeFn_toLp

end OAI.Analysis.Fourier.BochnerRiesz
