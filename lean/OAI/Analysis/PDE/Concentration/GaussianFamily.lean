import OAI.Analysis.PDE.Concentration.CompactJets
import OAI.Analysis.PDE.Green.LocalExtension

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter
open scoped ContDiff Topology

theorem exists_global_smooth_extension_near_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ ∀ x ∈ K, g =ᶠ[𝓝 x] f := by
  obtain ⟨χ, hχ, _, hone, hzero⟩ :=
    OAI.Analysis.PDE.Green.exists_smooth_cutoff_near_compact hK hU hKU (k := ⊤)
  refine ⟨fun x => χ x • f x, OAI.Analysis.PDE.Green.contDiff_cutoff_smul hU hχ hzero hf, ?_⟩
  intro x hx
  filter_upwards [hone x hx] with y hy
  simp only [hy, one_smul]

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- A local compact family has Gaussian bounds uniform in its parameters.
Only the Gaussian scale varies; the constant is chosen first. -/
theorem uniform_local_gaussian_jets {ψ : P × E → F}
    {K : Set P} {S : Set E} {U : Set (P × E)}
    (hK : IsCompact K) (hS : IsCompact S) (hU : IsOpen U)
    (hKU : K ×ˢ S ⊆ U) (hψ : ContDiffOn ℝ ∞ ψ U) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ x ∈ S, ∀ scale : ℝ, 1 ≤ scale →
      ∀ n ≤ N, ‖iteratedFDeriv ℝ n
        (fun y => standardGaussian (scale • ψ (p, y))) x‖ ≤ C * scale ^ n := by
  obtain ⟨g, hg, heq⟩ := exists_global_smooth_extension_near_compact
    (hK.prod hS) hU hKU hψ
  obtain ⟨B, hB, hb⟩ := compact_family_spatial_jets hg hK hS N
  obtain ⟨A, hA, ha⟩ := gaussian_scaled_composition_bound (E := E) (F := F) N
  let c : ℕ → ℝ := fun n => (n.factorial : ℝ) * A * B ^ n
  have hc (n : ℕ) : 0 ≤ c n := by dsimp [c]; positivity
  refine ⟨∑ n ∈ Finset.range (N + 1), c n, Finset.sum_nonneg (fun n _ => hc n), ?_⟩
  intro p hp x hx scale hscale n hn
  have hgp : ContDiff ℝ ∞ (fun y => g (p, y)) := hg.comp (contDiff_const.prodMk contDiff_id)
  have hbound := ha _ hgp B hB scale hscale n hn x
    (fun j _ hj => hb p hp x hx j (hj.trans hn))
  have he : (fun y => g (p, y)) =ᶠ[𝓝 x] (fun y => ψ (p, y)) :=
    (heq (p, x) ⟨hp, hx⟩).comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  have he' : (fun y => standardGaussian (scale • g (p, y))) =ᶠ[𝓝 x]
      (fun y => standardGaussian (scale • ψ (p, y))) := by
    filter_upwards [he] with y hy
    rw [hy]
  rw [← (he'.iteratedFDeriv ℝ n).self_of_nhds]
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun i _ => hc i) (Finset.mem_range.mpr (by omega)))
    (pow_nonneg (by linarith) n))

omit [MeasurableSpace F] [BorelSpace F] in
/-- Reciprocal Gaussian bounds on a bounded scaled observation patch. -/
theorem uniform_local_inverse_gaussian_jets {ψ : P × E → F}
    {K : Set P} {S : Set E} {U : Set (P × E)}
    (hK : IsCompact K) (hS : IsCompact S) (hU : IsOpen U)
    (hKU : K ×ˢ S ⊆ U) (hψ : ContDiffOn ℝ ∞ ψ U) (N : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ x ∈ S, ∀ scale : ℝ, 1 ≤ scale →
      ‖scale • ψ (p, x)‖ ≤ R → ∀ n ≤ N,
      ‖iteratedFDeriv ℝ n (fun y => inverseStandardGaussian (scale • ψ (p, y))) x‖ ≤
        C * scale ^ n := by
  obtain ⟨g, hg, heq⟩ := exists_global_smooth_extension_near_compact
    (hK.prod hS) hU hKU hψ
  obtain ⟨B, hB, hb⟩ := compact_family_spatial_jets hg hK hS N
  obtain ⟨A, hA, ha⟩ := inverse_gaussian_scaled_composition_bound (E := E) (F := F) N R
  let c : ℕ → ℝ := fun n => (n.factorial : ℝ) * A * B ^ n
  have hc (n : ℕ) : 0 ≤ c n := by dsimp [c]; positivity
  refine ⟨∑ n ∈ Finset.range (N + 1), c n, Finset.sum_nonneg (fun n _ => hc n), ?_⟩
  intro p hp x hx scale hscale hR n hn
  have hgp : ContDiff ℝ ∞ (fun y => g (p, y)) := hg.comp (contDiff_const.prodMk contDiff_id)
  have he : (fun y => g (p, y)) =ᶠ[𝓝 x] (fun y => ψ (p, y)) :=
    (heq (p, x) ⟨hp, hx⟩).comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  have hpoint : g (p, x) = ψ (p, x) := he.self_of_nhds
  have hRg : ‖scale • g (p, x)‖ ≤ R := by rwa [hpoint]
  have hbound := ha _ hgp B hB scale hscale n hn x hRg
    (fun j _ hj => hb p hp x hx j (hj.trans hn))
  have he' : (fun y => inverseStandardGaussian (scale • g (p, y))) =ᶠ[𝓝 x]
      (fun y => inverseStandardGaussian (scale • ψ (p, y))) := by
    filter_upwards [he] with y hy
    rw [hy]
  rw [← (he'.iteratedFDeriv ℝ n).self_of_nhds]
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun i _ => hc i) (Finset.mem_range.mpr (by omega)))
    (pow_nonneg (by linarith) n))

end OAI.Analysis.PDE.Concentration
