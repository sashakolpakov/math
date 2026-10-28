import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.MetricWeight
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Square Partition -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SquarePartition

noncomputable section

/-! A finite smooth partition normalized to have sum of squares equal to one, with unchanged supports. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {ι M : Type*} [Fintype ι]

def squarePartitionNormSq (f : ι → M → ℝ) (x : M) : ℝ := ∑ i, f i x ^ 2

def squarePartitionNormalized (f : ι → M → ℝ) (i : ι) (x : M) : ℝ :=
  f i x / Real.sqrt (squarePartitionNormSq f x)

theorem squarePartitionNormSq_pos (f : ι → M → ℝ) (hsum : ∀ x, ∑ i, f i x = 1) (x : M) :
    0 < squarePartitionNormSq f x := by
  classical
  have hsome : ∃ i, f i x ≠ 0 := by
    by_contra! hz
    have h := hsum x
    simp only [hz, Finset.sum_const_zero] at h
    exact zero_ne_one h
  obtain ⟨i, hi⟩ := hsome
  exact (sq_pos_of_ne_zero hi).trans_le
    (Finset.single_le_sum (fun j _ => sq_nonneg (f j x)) (Finset.mem_univ i))

theorem squarePartitionNormalized_sum_sq (f : ι → M → ℝ)
    (hsum : ∀ x, ∑ i, f i x = 1) (x : M) : ∑ i, squarePartitionNormalized f i x ^ 2 = 1 := by
  simp only [squarePartitionNormalized, div_pow, ← Finset.sum_div]
  rw [Real.sq_sqrt (squarePartitionNormSq_pos f hsum x).le]
  exact div_self (ne_of_gt (squarePartitionNormSq_pos f hsum x))

variable [TopologicalSpace M]

theorem squarePartitionNormalized_tsupport (f : ι → M → ℝ) (i : ι) :
    tsupport (squarePartitionNormalized f i) ⊆ tsupport (f i) := by
  apply closure_mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  simp only [squarePartitionNormalized, hx, zero_div]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E M]

theorem squarePartitionNormSq_smooth (f : ι → M → ℝ)
    (hf : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (f i)) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (squarePartitionNormSq f) := by
  apply ContMDiff.sum
  intro i _
  exact (hf i).pow 2

theorem squarePartitionNormalized_smooth (f : ι → M → ℝ)
    (hf : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (f i)) (hsum : ∀ x, ∑ i, f i x = 1) (i : ι) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (squarePartitionNormalized f i) := by
  have hd : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun x => Real.sqrt (squarePartitionNormSq f x)) := by
    intro x
    exact (Real.contDiffAt_sqrt (ne_of_gt (squarePartitionNormSq_pos f hsum x))).contMDiffAt.comp x
      (squarePartitionNormSq_smooth f hf x)
  exact (hf i).div₀ hd (fun x => ne_of_gt (Real.sqrt_pos.mpr (squarePartitionNormSq_pos f hsum x)))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SquarePartition
