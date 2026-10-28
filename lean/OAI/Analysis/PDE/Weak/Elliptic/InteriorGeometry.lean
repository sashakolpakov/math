import OAI.Analysis.PDE.Weak.Elliptic.H1
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Set _root_.MeasureTheory Filter Metric
open scoped Topology
namespace OAI.Analysis.PDE.Weak

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem exists_small_backward_shifts {S Ω : Set X} (hS : IsCompact S)
    (hΩ : IsOpen Ω) (hsub : S ⊆ Ω) (v : X) (hv : ‖v‖ ≤ 1) :
    ∃ s : ℕ → ℝ, Tendsto s atTop (𝓝 0) ∧ (∀ n, s n ≠ 0) ∧
      ∀ n, (fun x ↦ x + (-s n) • v) ⁻¹' S ⊆ Ω := by
  obtain ⟨δ, hδ, hthick⟩ := hS.exists_cthickening_subset_open hΩ hsub
  let s : ℕ → ℝ := fun n ↦ δ / ((n : ℝ) + 1)
  have hspos : ∀ n, 0 < s n := fun n ↦ div_pos hδ (by positivity)
  have hsbound : ∀ n, s n ≤ δ := by
    intro n
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  refine ⟨s, ?_, fun n ↦ (hspos n).ne', ?_⟩
  · have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
    simpa [s, div_eq_mul_inv] using ht
  · intro n x hx
    change x + (-s n) • v ∈ S at hx
    apply hthick
    apply closedBall_subset_cthickening hx δ
    change dist x (x + (-s n) • v) ≤ δ
    simp only [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hspos n)]
    exact (mul_le_mul_of_nonneg_left hv (hspos n).le).trans (by simpa using hsbound n)

end OAI.Analysis.PDE.Weak
