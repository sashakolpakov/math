import OAI.Analysis.PDE.Concentration.InverseGaussian

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set
open scoped ContDiff

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_partial_le {f : P × E → F} (hf : ContDiff ℝ ∞ f)
    (p : P) (x : E) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => f (p, y)) x‖ ≤ ‖iteratedFDeriv ℝ n f (p, x)‖ := by
  let L : E →L[ℝ] P × E := ContinuousLinearMap.inr ℝ P E
  have ht : ContDiff ℝ ∞ (fun y : P × E => f ((p, 0) + y)) :=
    hf.comp (contDiff_const.add contDiff_id)
  have he : (fun y => f (p, y)) = (fun y : P × E => f ((p, 0) + y)) ∘ L := by
    ext y
    simp [L]
  rw [he, L.iteratedFDeriv_comp_right ht x (by simp), iteratedFDeriv_comp_add_left]
  have hb := (iteratedFDeriv ℝ n f ((p, 0) + L x)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hb
  have hn : ‖L‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg L) (ContinuousLinearMap.norm_inr_le_one ℝ P E)
  have hh := hb.trans (mul_le_of_le_one_right (norm_nonneg _) hn)
  simpa [L] using hh

/-- All spatial derivatives of a smooth compact parameter family are
uniformly bounded on a fixed compact frequency set. -/
theorem compact_family_spatial_jets {f : P × E → F} (hf : ContDiff ℝ ∞ f)
    {K : Set P} {S : Set E} (hK : IsCompact K) (hS : IsCompact S) (N : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ p ∈ K, ∀ x ∈ S, ∀ n ≤ N,
      ‖iteratedFDeriv ℝ n (fun y => f (p, y)) x‖ ≤ B := by
  obtain ⟨C, hC, hc⟩ := compact_smooth_jets_bound hf (hK.prod hS) N
  refine ⟨C + 1, by linarith, ?_⟩
  intro p hp x hx n hn
  exact (norm_iteratedFDeriv_partial_le hf p x n).trans ((hc n hn _ ⟨hp, hx⟩).trans (by linarith))

end OAI.Analysis.PDE.Concentration
