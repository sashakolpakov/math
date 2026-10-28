import OAI.Analysis.Fourier.BochnerRiesz.BoundedFamily

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz


abbrev BrBoundedLp (n : ℕ) (p : ℝ≥0∞) :=
  Lp (α := Space n) (BoundedContinuousFunction PositiveRadius ℂ) p volume

theorem brBoundedFamily_add {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (f g : SchwartzMap (Space n) ℂ) :
    brBoundedFamily hδ (f + g) = brBoundedFamily hδ f + brBoundedFamily hδ g := by
  funext x
  ext R
  exact congrFun (bochnerRiesz_schwartz_add hδ R f g) x

theorem brBoundedFamily_smul {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (c : ℂ) (f : SchwartzMap (Space n) ℂ) :
    brBoundedFamily hδ (c • f) = c • brBoundedFamily hδ f := by
  funext x
  ext R
  exact congrFun (bochnerRiesz_schwartz_smul δ R c f) x

def brBoundedSchwartzToLp {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hLp : ∀ f : SchwartzMap (Space n) ℂ, MemLp (brBoundedFamily hδ f) p volume) :
    SchwartzMap (Space n) ℂ →ₗ[ℂ] BrBoundedLp n p where
  toFun f := (hLp f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(hLp (f + g)).coeFn_toLp, (hLp f).coeFn_toLp, (hLp g).coeFn_toLp,
      Lp.coeFn_add ((hLp f).toLp _) ((hLp g).toLp _)] with x hfg hf hg hs
    rw [hfg, hs, Pi.add_apply, hf, hg]
    exact congrFun (brBoundedFamily_add hδ f g) x
  map_smul' c f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [(hLp (c • f)).coeFn_toLp, (hLp f).coeFn_toLp,
      Lp.coeFn_smul c ((hLp f).toLp _)] with x hcf hf hs
    rw [hcf, hs, Pi.smul_apply, hf]
    exact congrFun (brBoundedFamily_smul hδ c f) x

def brBoundedLpExtend {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hLp : ∀ f : SchwartzMap (Space n) ℂ, MemLp (brBoundedFamily hδ f) p volume) :
    BrLp n p →L[ℂ] BrBoundedLp n p :=
  (brBoundedSchwartzToLp hδ hLp).extendOfNorm
    (SchwartzMap.toLpCLM ℂ ℂ p volume).toLinearMap

theorem brBoundedLpExtend_properties {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hpt : p ≠ ⊤) {δ : ℝ} (hδ : 0 ≤ δ)
    (hLp : ∀ f : SchwartzMap (Space n) ℂ, MemLp (brBoundedFamily hδ f) p volume)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ f : SchwartzMap (Space n) ℂ, eLpNorm (brBoundedFamily hδ f) p volume ≤
      ENNReal.ofReal C * eLpNorm f p volume) :
    ‖brBoundedLpExtend hδ hLp‖ ≤ C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      brBoundedLpExtend hδ hLp (f.toLp p volume) = (hLp f).toLp _ := by
  have hd : DenseRange (SchwartzMap.toLpCLM ℂ ℂ p (volume : Measure (Space n))).toLinearMap :=
    SchwartzMap.denseRange_toLpCLM hpt
  have hnorm (f : SchwartzMap (Space n) ℂ) :
      ‖brBoundedSchwartzToLp hδ hLp f‖ ≤ C * ‖f.toLp p volume‖ := by
    change ‖(hLp f).toLp _‖ ≤ _
    rw [Lp.norm_toLp, SchwartzMap.norm_toLp]
    have H := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (f.memLp p volume).ne) (hb f)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using H
  exact ⟨LinearMap.opNorm_extendOfNorm_le hd hC hnorm,
    fun f => LinearMap.extendOfNorm_eq hd ⟨C, hnorm⟩ f⟩

def brBoundedEval {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (R : PositiveRadius) :
    BrBoundedLp n p →L[ℂ] BrLp n p :=
  (BoundedContinuousFunction.evalCLM (𝕜 := ℂ) R).compLpL p volume

theorem brBoundedEval_coe {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (R : PositiveRadius) (F : BrBoundedLp n p) :
    (brBoundedEval R F : Space n → ℂ) =ᵐ[volume] (fun x => F x R) := by
  let L : BoundedContinuousFunction PositiveRadius ℂ →L[ℂ] ℂ :=
    BoundedContinuousFunction.evalCLM (𝕜 := ℂ) R
  have h := L.coeFn_compLpL (μ := volume) (p := p) F
  change (brBoundedEval R F : Space n → ℂ) =ᵐ[volume] (fun x => L (F x))
  exact h

theorem localSmoothing_brBoundedLp_operator (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {p δ : ℝ} (hp : 2 ≤ p)
    [Fact (1 ≤ ENNReal.ofReal p)] (hδ : OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ U : BrLp n (ENNReal.ofReal p) →L[ℂ] BrBoundedLp n (ENNReal.ofReal p),
      ‖U‖ ≤ C ∧
      (∀ f : SchwartzMap (Space n) ℂ,
        (U (f.toLp (ENNReal.ofReal p) volume) : Space n → BoundedContinuousFunction PositiveRadius ℂ) =ᵐ[volume]
          brBoundedFamily ((le_max_left _ _).trans hδ.le) f) := by
  obtain ⟨C, hC, hb⟩ := OAI.Analysis.Fourier.SquareFunction.localSmoothing_maximalBochnerRiesz hls hn hp hδ
  let hd : 0 ≤ δ := (le_max_left _ _).trans hδ.le
  have hLp (f : SchwartzMap (Space n) ℂ) : MemLp (brBoundedFamily hd f) (ENNReal.ofReal p) volume := by
    change eLpNorm _ _ _ < ⊤
    rw [eLpNorm_brBoundedFamily]
    exact (hb f).1
  have hbound (f : SchwartzMap (Space n) ℂ) : eLpNorm (brBoundedFamily hd f) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
    rw [eLpNorm_brBoundedFamily]
    exact (hb f).2
  let U := brBoundedLpExtend hd hLp
  obtain ⟨hUnorm, hUeq⟩ := brBoundedLpExtend_properties ENNReal.ofReal_ne_top hd hLp hC.le hbound
  refine ⟨C, hC, U, hUnorm, fun f => ?_⟩
  rw [show U (f.toLp (ENNReal.ofReal p) volume) = (hLp f).toLp _ from hUeq f]
  exact (hLp f).coeFn_toLp

end OAI.Analysis.Fourier.BochnerRiesz
