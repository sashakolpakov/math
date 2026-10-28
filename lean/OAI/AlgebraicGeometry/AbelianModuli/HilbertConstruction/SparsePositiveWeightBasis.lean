import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SparseHighWeightSpanning
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisWithMarkedLabel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MarkedThresholdPositiveSum
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Sparse Positive Weight Basis -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SparsePositiveWeightBasis

noncomputable section

/-! For a sparse configuration, every zero-sum weighting with a
positive maximum has a basis with positive total weight. This is the
dual obstruction required in the determinant-cone argument. -/
open scoped BigOperators Classical
universe u v
variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
variable {ι : Type v} [Fintype ι]

theorem sparseFamily_positiveWeightBasis (v : ι → V)
    (hr : 2 ≤ Module.finrank K V)
    (hs : ∀ W : Submodule K V, W ≠ ⊤ → Module.finrank K V *
      (Finset.univ.filter (fun i => v i ∈ W)).card < Fintype.card ι)
    (a : ι → ℝ) (ha : ∑ i, a i = 0) (i₀ : ι) (hv₀ : v i₀ ≠ 0)
    (ha₀ : 0 < a i₀) (hmax : ∀ i, a i ≤ a i₀) :
    ∃ (κ : Type u) (_ : Fintype κ) (b : Module.Basis κ K V) (σ : κ → ι),
      (∀ j, v (σ j) = b j) ∧ 0 < ∑ j, a (σ j) := by
  let H := {i | -a i₀ < ((Module.finrank K V : ℝ) - 1) * a i}
  have hspan := SparseHighWeightSpanning.sparse_highWeight_labels_span v (Module.finrank K V) (by omega)
    hs a ha (a i₀) ha₀ hmax
  have hi₀ : i₀ ∈ H := by
    have hr' : (2 : ℝ) ≤ Module.finrank K V := by exact_mod_cast hr
    change -a i₀ < ((Module.finrank K V : ℝ) - 1) * a i₀
    nlinarith
  obtain ⟨κ, hκ, b, σ, j₀, hσ, hb, hj₀⟩ :=
    BasisWithMarkedLabel.spanningFamily_basis_containing_label v H hspan i₀ hi₀ hv₀
  let : Fintype κ := hκ
  have hcard : Fintype.card κ = Module.finrank K V := (Module.finrank_eq_card_basis b).symm
  refine ⟨κ, hκ, b, σ, hb, MarkedThresholdPositiveSum.markedThreshold_sum_pos (hcard.symm ▸ hr)
    (fun j => a (σ j)) j₀ (a i₀) ha₀ (congrArg a hj₀) ?_⟩
  intro j _
  simpa only [hcard] using (show -a i₀ < ((Module.finrank K V : ℝ) - 1) * a (σ j) from hσ j)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SparsePositiveWeightBasis
