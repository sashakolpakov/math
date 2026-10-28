import OAI.Analysis.PDE.Concentration.GaussianPhase

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter
open scoped ContDiff Topology
open OAI.Analysis.Calculus.Current

def gaussianB0 {d : ℕ} (p : TransverseSpace d × OAI.Analysis.Calculus.Current.SpatialSpace d) : ℝ :=
  (1 + inner ℝ (gaussianVelocity p.2) p.1 / 2) / Real.sqrt 2

def gaussianB1 {d : ℕ} (p : TransverseSpace d × OAI.Analysis.Calculus.Current.SpatialSpace d) : ℝ :=
  (inner ℝ (Complex.I • gaussianVelocity p.2) p.1 / 2) / Real.sqrt 2

def gaussianB {d : ℕ} (j : Fin 2) (p : TransverseSpace d × OAI.Analysis.Calculus.Current.SpatialSpace d) : ℝ :=
  if j = 0 then gaussianB0 p else gaussianB1 p

def gaussianForwardAmplitude {d : ℕ} (j : Fin 2)
    (p : TransverseSpace d × OAI.Analysis.Calculus.Current.SpatialSpace d) : ℂ :=
  (gaussianB j p * (gaussianFrequencyK p.2) ^ ((d : ℝ) / 2) : ℝ)

def gaussianInverseAmplitude {d : ℕ} (p : TransverseSpace d × OAI.Analysis.Calculus.Current.SpatialSpace d) : ℂ :=
  ((gaussianB0 p)⁻¹ * (gaussianFrequencyK p.2) ^ (-(d : ℝ) / 2) : ℝ)

theorem contDiffAt_gaussianB0 {d : ℕ} {p : TransverseSpace d × OAI.Analysis.Calculus.Current.SpatialSpace d}
    (hp : 0 < gaussianFrequencyK p.2) : ContDiffAt ℝ ∞ gaussianB0 p := by
  have hU : IsOpen {η : OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianFrequencyK η} :=
    isOpen_lt continuous_const continuous_gaussianFrequencyK
  have hv := ((contDiffOn_gaussianVelocity p.2 hp).contDiffAt (hU.mem_nhds hp)).comp p contDiffAt_snd
  exact (contDiffAt_const.add ((hv.inner ℝ contDiffAt_fst).div_const _)).div_const _

theorem contDiffAt_gaussianB1 {d : ℕ} {p : TransverseSpace d × OAI.Analysis.Calculus.Current.SpatialSpace d}
    (hp : 0 < gaussianFrequencyK p.2) : ContDiffAt ℝ ∞ gaussianB1 p := by
  have hU : IsOpen {η : OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianFrequencyK η} :=
    isOpen_lt continuous_const continuous_gaussianFrequencyK
  have hv := ((contDiffOn_gaussianVelocity p.2 hp).contDiffAt (hU.mem_nhds hp)).comp p contDiffAt_snd
  exact (((hv.const_smul Complex.I).inner ℝ contDiffAt_fst).div_const _).div_const _

theorem contDiffAt_gaussianB {d : ℕ} (j : Fin 2) {p : TransverseSpace d × OAI.Analysis.Calculus.Current.SpatialSpace d}
    (hp : 0 < gaussianFrequencyK p.2) : ContDiffAt ℝ ∞ (gaussianB j) p := by
  by_cases hj : j = 0
  · have he : gaussianB (d := d) j = gaussianB0 := by ext q; simp [gaussianB, hj]
    rw [he]
    exact contDiffAt_gaussianB0 hp
  · have he : gaussianB (d := d) j = gaussianB1 := by ext q; simp [gaussianB, hj]
    rw [he]
    exact contDiffAt_gaussianB1 hp

theorem gaussianB0_pos_of_small {d : ℕ} {W : TransverseSpace d} {η : OAI.Analysis.Calculus.Current.SpatialSpace d}
    (hW : ‖W‖ ≤ 1) (hv : ‖gaussianVelocity η‖ ≤ 1) : 0 < gaussianB0 (W, η) := by
  have hi := neg_le_of_abs_le (abs_real_inner_le_norm (gaussianVelocity η) W)
  have hn : ‖gaussianVelocity η‖ * ‖W‖ ≤ 1 :=
    (mul_le_mul hv hW (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  apply div_pos _ (Real.sqrt_pos.2 (by norm_num))
  dsimp at hi ⊢
  linarith

theorem contDiffOn_gaussianForwardAmplitude {d : ℕ} (j : Fin 2) :
    ContDiffOn ℝ ∞ (gaussianForwardAmplitude (d := d) j)
      {p | 0 < gaussianFrequencyK p.2} := by
  intro p hp
  have hk := (contDiffAt_gaussianFrequencyK (gaussianFrequencyK_ne_zero_frequency hp)).comp p contDiffAt_snd
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp p
    ((contDiffAt_gaussianB j hp).mul (hk.rpow_const_of_ne hp.ne'))).contDiffWithinAt

theorem contDiffOn_gaussianInverseAmplitude {d : ℕ} :
    ContDiffOn ℝ ∞ (gaussianInverseAmplitude (d := d))
      {p | 0 < gaussianFrequencyK p.2 ∧ 0 < gaussianB0 p} := by
  intro p hp
  have hk := (contDiffAt_gaussianFrequencyK (gaussianFrequencyK_ne_zero_frequency hp.1)).comp p contDiffAt_snd
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp p
    (((contDiffAt_gaussianB0 hp.1).inv hp.2.ne').mul (hk.rpow_const_of_ne hp.1.ne'))).contDiffWithinAt

/-- Compact local families have uniform derivative bounds without requiring
an extension to be supplied as an extra hypothesis. -/
theorem compact_local_family_spatial_jets
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : P × E → F} {K : Set P} {S : Set E} {U : Set (P × E)}
    (hK : IsCompact K) (hS : IsCompact S) (hU : IsOpen U) (hKU : K ×ˢ S ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ x ∈ S, ∀ n ≤ N,
      ‖iteratedFDeriv ℝ n (fun y => f (p, y)) x‖ ≤ C := by
  obtain ⟨g, hg, he⟩ := exists_global_smooth_extension_near_compact (hK.prod hS) hU hKU hf
  obtain ⟨C, hC, hc⟩ := compact_family_spatial_jets hg hK hS N
  refine ⟨C, by linarith, ?_⟩
  intro p hp x hx n hn
  have he' : (fun y => g (p, y)) =ᶠ[𝓝 x] (fun y => f (p, y)) :=
    (he (p, x) ⟨hp, hx⟩).comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  rw [← (he'.iteratedFDeriv ℝ n).self_of_nhds]
  exact hc p hp x hx n hn

end OAI.Analysis.PDE.Concentration
