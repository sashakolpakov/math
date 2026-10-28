import OAI.Analysis.Fourier.BochnerRiesz.CompactNorm

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz


abbrev BrFamilyLp (n : ℕ) (p : ℝ≥0∞) := Lp (α := Space n) C(InverseRadius, ℂ) p volume

theorem brCompactFamily_add {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (f g : SchwartzMap (Space n) ℂ) :
    brCompactFamily hδ (f + g) = brCompactFamily hδ f + brCompactFamily hδ g := by
  funext x
  ext τ
  by_cases hτ : (τ : ℝ) = 0
  · have ht : τ = inverseRadiusZero := Subtype.ext hτ
    simp only [ht, Pi.add_apply, ContinuousMap.add_apply, brCompactFamily_zero,
      add_apply]
  · have ht : 0 < (τ : ℝ) := lt_of_le_of_ne τ.property.1 (Ne.symm hτ)
    simp only [Pi.add_apply, ContinuousMap.add_apply, brCompactFamily_pos hδ _ _ τ ht]
    exact congrFun (bochnerRiesz_schwartz_add hδ (τ : ℝ)⁻¹ f g) x

theorem brCompactFamily_smul {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (c : ℂ) (f : SchwartzMap (Space n) ℂ) :
    brCompactFamily hδ (c • f) = c • brCompactFamily hδ f := by
  funext x
  ext τ
  by_cases hτ : (τ : ℝ) = 0
  · have ht : τ = inverseRadiusZero := Subtype.ext hτ
    simp only [ht, Pi.smul_apply, ContinuousMap.smul_apply, brCompactFamily_zero,
      smul_apply]
  · have ht : 0 < (τ : ℝ) := lt_of_le_of_ne τ.property.1 (Ne.symm hτ)
    simp only [Pi.smul_apply, ContinuousMap.smul_apply, brCompactFamily_pos hδ _ _ τ ht]
    exact congrFun (bochnerRiesz_schwartz_smul δ (τ : ℝ)⁻¹ c f) x

def brFamilySchwartzToLp {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hLp : ∀ f : SchwartzMap (Space n) ℂ, MemLp (brCompactFamily hδ f) p volume) :
    SchwartzMap (Space n) ℂ →ₗ[ℂ] BrFamilyLp n p where
  toFun f := (hLp f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(hLp (f + g)).coeFn_toLp, (hLp f).coeFn_toLp, (hLp g).coeFn_toLp,
      Lp.coeFn_add ((hLp f).toLp _) ((hLp g).toLp _)] with x hfg hf hg hs
    rw [hfg, hs, Pi.add_apply, hf, hg]
    exact congrFun (brCompactFamily_add hδ f g) x
  map_smul' c f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [(hLp (c • f)).coeFn_toLp, (hLp f).coeFn_toLp,
      Lp.coeFn_smul c ((hLp f).toLp _)] with x hcf hf hs
    rw [hcf, hs, Pi.smul_apply, hf]
    exact congrFun (brCompactFamily_smul hδ c f) x

def brFamilyLpExtend {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hLp : ∀ f : SchwartzMap (Space n) ℂ, MemLp (brCompactFamily hδ f) p volume) :
    BrLp n p →L[ℂ] BrFamilyLp n p :=
  (brFamilySchwartzToLp hδ hLp).extendOfNorm
    (SchwartzMap.toLpCLM ℂ ℂ p volume).toLinearMap

theorem brFamilyLpExtend_properties {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hpt : p ≠ ⊤) {δ : ℝ} (hδ : 0 ≤ δ)
    (hLp : ∀ f : SchwartzMap (Space n) ℂ, MemLp (brCompactFamily hδ f) p volume)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ f : SchwartzMap (Space n) ℂ, eLpNorm (brCompactFamily hδ f) p volume ≤
      ENNReal.ofReal C * eLpNorm f p volume) :
    ‖brFamilyLpExtend hδ hLp‖ ≤ C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      brFamilyLpExtend hδ hLp (f.toLp p volume) = (hLp f).toLp _ := by
  have hd : DenseRange (SchwartzMap.toLpCLM ℂ ℂ p (volume : Measure (Space n))).toLinearMap :=
    SchwartzMap.denseRange_toLpCLM hpt
  have hnorm (f : SchwartzMap (Space n) ℂ) :
      ‖brFamilySchwartzToLp hδ hLp f‖ ≤ C * ‖f.toLp p volume‖ := by
    change ‖(hLp f).toLp _‖ ≤ _
    rw [Lp.norm_toLp, SchwartzMap.norm_toLp]
    have H := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (f.memLp p volume).ne) (hb f)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using H
  exact ⟨LinearMap.opNorm_extendOfNorm_le hd hC hnorm,
    fun f => LinearMap.extendOfNorm_eq hd ⟨C, hnorm⟩ f⟩

def brFamilyEval {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (τ : InverseRadius) :
    BrFamilyLp n p →L[ℂ] BrLp n p :=
  (ContinuousMap.evalCLM ℂ τ).compLpL p volume

theorem brFamilyEval_coe {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (τ : InverseRadius) (F : BrFamilyLp n p) :
    (brFamilyEval τ F : Space n → ℂ) =ᵐ[volume] (fun x => F x τ) := by
  let L : C(InverseRadius, ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ τ
  have h := L.coeFn_compLpL (μ := volume) (p := p) F
  change (brFamilyEval τ F : Space n → ℂ) =ᵐ[volume] (fun x => L (F x))
  exact h

theorem brFamily_zero_eval_of_schwartz {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hpt : p ≠ ⊤) {δ : ℝ} (hδ : 0 ≤ δ)
    (U : BrLp n p →L[ℂ] BrFamilyLp n p)
    (hU : ∀ f : SchwartzMap (Space n) ℂ,
      (U (f.toLp p volume) : Space n → C(InverseRadius, ℂ)) =ᵐ[volume] brCompactFamily hδ f) :
    ∀ f : BrLp n p, brFamilyEval inverseRadiusZero (U f) = f := by
  have hd : DenseRange (fun f : SchwartzMap (Space n) ℂ => f.toLp p volume) :=
    SchwartzMap.denseRange_toLpCLM hpt
  have hbase (f : SchwartzMap (Space n) ℂ) :
      brFamilyEval inverseRadiusZero (U (f.toLp p volume)) = f.toLp p volume := by
    apply Lp.ext
    filter_upwards [brFamilyEval_coe inverseRadiusZero (U (f.toLp p volume)), hU f,
      (f.memLp p volume).coeFn_toLp] with x hx hu hf
    rw [hx, hu, brCompactFamily_zero]
    exact hf.symm
  have he : (fun f => brFamilyEval inverseRadiusZero (U f)) = (fun f : BrLp n p => f) :=
    hd.equalizer ((brFamilyEval inverseRadiusZero).continuous.comp U.continuous)
      continuous_id (funext hbase)
  exact fun f => congrFun he f

/-- A bounded operator carrying the whole large-radius family, including
its limiting value, into a space of continuous functions. -/
theorem localSmoothing_brFamilyLp_operator (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {p δ : ℝ} (hp : 2 ≤ p)
    [Fact (1 ≤ ENNReal.ofReal p)] (hδ : OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ U : BrLp n (ENNReal.ofReal p) →L[ℂ] BrFamilyLp n (ENNReal.ofReal p),
      ‖U‖ ≤ C ∧
      (∀ f : SchwartzMap (Space n) ℂ,
        (U (f.toLp (ENNReal.ofReal p) volume) : Space n → C(InverseRadius, ℂ)) =ᵐ[volume]
          brCompactFamily ((le_max_left _ _).trans hδ.le) f) ∧
      (∀ f : BrLp n (ENNReal.ofReal p), brFamilyEval inverseRadiusZero (U f) = f) := by
  obtain ⟨C, hC, hb⟩ := localSmoothing_brCompactFamily_bound hls hn hp hδ
  let hLp := fun f : SchwartzMap (Space n) ℂ => (hb f).1
  let hd : 0 ≤ δ := (le_max_left _ _).trans hδ.le
  let U := brFamilyLpExtend hd hLp
  obtain ⟨hUnorm, hUeq⟩ := brFamilyLpExtend_properties ENNReal.ofReal_ne_top hd hLp hC.le (fun f => (hb f).2)
  have hU (f : SchwartzMap (Space n) ℂ) :
      (U (f.toLp (ENNReal.ofReal p) volume) : Space n → C(InverseRadius, ℂ)) =ᵐ[volume]
        brCompactFamily hd f := by
    rw [show U (f.toLp (ENNReal.ofReal p) volume) = (hLp f).toLp _ from hUeq f]
    exact (hLp f).coeFn_toLp
  exact ⟨C, hC, U, hUnorm, hU, brFamily_zero_eval_of_schwartz ENNReal.ofReal_ne_top hd U hU⟩

end OAI.Analysis.Fourier.BochnerRiesz
