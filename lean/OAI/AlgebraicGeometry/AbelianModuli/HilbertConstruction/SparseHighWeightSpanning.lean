import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SumHighWeightCount
import Mathlib.LinearAlgebra.Span.Basic

/-! # Sparse High Weight Spanning -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SparseHighWeightSpanning

noncomputable section

/-! Hyperplane sparsity implies that the high-weight labels span.
This is the geometric input to the determinant cone separation argument. -/
open scoped BigOperators Classical
universe u v
variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
variable {ι : Type v} [Fintype ι]

theorem sparse_highWeight_labels_span (v : ι → V) (r : ℕ) (hr : 1 ≤ r)
    (hs : ∀ W : Submodule K V, W ≠ ⊤ →
      r * (Finset.univ.filter (fun i => v i ∈ W)).card < Fintype.card ι)
    (a : ι → ℝ) (ha : ∑ i, a i = 0) (M : ℝ) (hM : 0 < M) (hmax : ∀ i, a i ≤ M) :
    Submodule.span K (v '' {i | -M < ((r : ℝ) - 1) * a i}) = ⊤ := by
  let H := Finset.univ.filter (fun i => -M < ((r : ℝ) - 1) * a i)
  let W := Submodule.span K (v '' {i | -M < ((r : ℝ) - 1) * a i})
  by_contra hW
  have hsub : H ⊆ Finset.univ.filter (fun i => v i ∈ W) := by
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, Submodule.subset_span ?_⟩
    exact ⟨i, (Finset.mem_filter.mp hi).2, rfl⟩
  have hcount := SumHighWeightCount.zeroSum_strictHighWeight_count a ha M hM hmax r hr
  have hlt := hs W hW
  have hle := Nat.mul_le_mul_left r (Finset.card_le_card hsub)
  exact (not_lt_of_ge (hcount.trans hle)) hlt

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SparseHighWeightSpanning
