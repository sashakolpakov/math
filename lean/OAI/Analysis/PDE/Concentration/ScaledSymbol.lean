import OAI.Analysis.PDE.Concentration.GaussianFamily

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter
open scoped ContDiff Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem bounded_outer_scaled_composition {χ : F → G} (hχ : ContDiff ℝ ∞ χ)
    {C : ℝ} {N : ℕ} (hC : ∀ j ≤ N, ∀ y, ‖iteratedFDeriv ℝ j χ y‖ ≤ C)
    {ψ : E → F} (hψ : ContDiff ℝ ∞ ψ) {B scale : ℝ} (hB : 1 ≤ B) (hs : 1 ≤ scale)
    (x : E) {n : ℕ} (hn : n ≤ N)
    (hb : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j ψ x‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun y => χ (scale • ψ y)) x‖ ≤
      (n.factorial : ℝ) * C * B ^ n * scale ^ n := by
  have hh := norm_iteratedFDeriv_comp_le hχ (hψ.const_smul scale) (by simp) x
    (fun j hj => hC j (hj.trans hn) _) (D := B * scale) (fun j hj hjn => ?_)
  · simpa only [Function.comp_def, mul_pow, mul_assoc] using hh
  · change ‖iteratedFDeriv ℝ j (scale • ψ) x‖ ≤ (B * scale) ^ j
    rw [iteratedFDeriv_const_smul_apply (hψ.of_le (by simp)).contDiffAt,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ scale)]
    calc
      _ ≤ scale * B := mul_le_mul_of_nonneg_left (hb j hj hjn) (by linarith)
      _ ≤ scale ^ j * B ^ j := mul_le_mul (le_self_pow₀ hs (by omega))
        (le_self_pow₀ hB (by omega)) (by linarith) (by positivity)
      _ = (B * scale) ^ j := by rw [mul_pow]; ring

/-- A fixed compact smooth outer symbol can be rescaled by an arbitrarily
large factor; the constants depend only on the fixed data. -/
theorem local_scaled_compact_symbol_jets [FiniteDimensional ℝ E]
    {χ : F → G} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    {ψ : E → F} {S U : Set E} (hS : IsCompact S) (hU : IsOpen U) (hSU : S ⊆ U)
    (hψ : ContDiffOn ℝ ∞ ψ U) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ scale : ℝ, 1 ≤ scale → ∀ n ≤ N,
      ‖iteratedFDeriv ℝ n (fun y => χ (scale • ψ y)) x‖ ≤ C * scale ^ n := by
  obtain ⟨g, hg, he⟩ := exists_global_smooth_extension_near_compact hS hU hSU hψ
  obtain ⟨B₀, hB₀, hb⟩ := compact_smooth_jets_bound hg hS N
  let B := B₀ + 1
  have hB : 1 ≤ B := by dsimp [B]; linarith
  obtain ⟨A, hA, ha⟩ := hcχ.exists_bound_iteratedFDeriv hχ N
  let c : ℕ → ℝ := fun n => (n.factorial : ℝ) * A * B ^ n
  have hc (n : ℕ) : 0 ≤ c n := by dsimp [c]; positivity
  refine ⟨∑ n ∈ Finset.range (N + 1), c n, Finset.sum_nonneg (fun n _ => hc n), ?_⟩
  intro x hx scale hs n hn
  have hbound := bounded_outer_scaled_composition hχ ha hg hB hs x hn
    (fun j _ hj => (hb j (hj.trans hn) x hx).trans (by dsimp [B]; linarith))
  have he' : (fun y => χ (scale • g y)) =ᶠ[𝓝 x] (fun y => χ (scale • ψ y)) := by
    filter_upwards [he x hx] with y hy
    rw [hy]
  rw [← (he'.iteratedFDeriv ℝ n).self_of_nhds]
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun i _ => hc i) (Finset.mem_range.mpr (by omega)))
    (pow_nonneg (by linarith) n))

end OAI.Analysis.PDE.Concentration
