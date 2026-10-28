import OAI.Analysis.PDE.Concentration.GaussianFamily

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The product rule preserves one power of the scale per derivative. -/
theorem scaled_product_jets {f g : E → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {A B scale : ℝ} (hA : 0 ≤ A) (_ : 0 ≤ B) (hs : 0 ≤ scale)
    (x : E) (n : ℕ)
    (hb_f : ∀ j ≤ n, ‖iteratedFDeriv ℝ j f x‖ ≤ A * scale ^ j)
    (hb_g : ∀ j ≤ n, ‖iteratedFDeriv ℝ j g x‖ ≤ B * scale ^ j) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤ 2 ^ n * A * B * scale ^ n := by
  have hb := norm_iteratedFDeriv_mul_le hf hg x (n := n) (by simp)
  have hc : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ := hb
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (A * scale ^ i) *
        (B * scale ^ (n - i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hb_f i hin) (Nat.cast_nonneg _))
        (hb_g _ (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (A * B * scale ^ n) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [show (n.choose i : ℝ) * (A * scale ^ i) * (B * scale ^ (n - i)) =
        (n.choose i : ℝ) * (A * B * (scale ^ i * scale ^ (n - i))) by ring,
        ← pow_add, Nat.add_sub_of_le hin]
    _ = 2 ^ n * A * B * scale ^ n := by rw [← Finset.sum_mul, hc]; ring

/-- Local smoothness suffices for the product estimate. This avoids imposing
artificial regularity at the excluded zero frequency. -/
theorem local_scaled_product_jets {f g : E → ℂ} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {A B scale : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 ≤ scale)
    {x : E} (hx : x ∈ U) (n : ℕ)
    (hb_f : ∀ j ≤ n, ‖iteratedFDeriv ℝ j f x‖ ≤ A * scale ^ j)
    (hb_g : ∀ j ≤ n, ‖iteratedFDeriv ℝ j g x‖ ≤ B * scale ^ j) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤ 2 ^ n * A * B * scale ^ n := by
  obtain ⟨f', hf', hef⟩ := exists_global_smooth_extension_near_compact
    (isCompact_singleton (x := x)) hU (singleton_subset_iff.mpr hx) hf
  obtain ⟨g', hg', heg⟩ := exists_global_smooth_extension_near_compact
    (isCompact_singleton (x := x)) hU (singleton_subset_iff.mpr hx) hg
  have hef' := hef x (mem_singleton x)
  have heg' := heg x (mem_singleton x)
  have hb := scaled_product_jets hf' hg' hA hB hs x n
    (fun j hj => by rw [(hef'.iteratedFDeriv ℝ j).self_of_nhds]; exact hb_f j hj)
    (fun j hj => by rw [(heg'.iteratedFDeriv ℝ j).self_of_nhds]; exact hb_g j hj)
  change ‖iteratedFDeriv ℝ n (f' * g') x‖ ≤ _ at hb
  rw [((hef'.mul heg').iteratedFDeriv ℝ n).self_of_nhds] at hb
  exact hb

end OAI.Analysis.PDE.Concentration
