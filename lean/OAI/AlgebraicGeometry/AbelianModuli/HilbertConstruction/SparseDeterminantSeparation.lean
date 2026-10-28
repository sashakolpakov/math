import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SparsePositiveWeightBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroSumPositiveMaximum
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LabeledDeterminantPolynomials

/-! # Sparse Determinant Separation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SparseDeterminantSeparation

noncomputable section

/-! Every nonzero zero-sum linear weight is positive on a nonvanishing
maximal determinant of a sparse configuration. This is the precise
finite determinant incidence statement used to construct the quotient. -/
open scoped BigOperators Classical
universe u
variable {K : Type u} [Field K] {r m : ℕ}

theorem sparseConfiguration_determinant_separates_zeroSum_weight
    (v : Fin m → Fin r → K) (hv : ∀ i, v i ≠ 0) (hr : 2 ≤ r)
    (hs : ∀ W : Submodule K (Fin r → K), W ≠ ⊤ →
      r * (Finset.univ.filter (fun i => v i ∈ W)).card < m)
    (a : Fin m → ℝ) (ha : ∑ i, a i = 0) (hne : a ≠ 0) :
    ∃ σ : Fin r → Fin m, LabeledDeterminantPolynomials.labeledDeterminant σ v ≠ 0 ∧ 0 < ∑ j, a (σ j) := by
  obtain ⟨i₀, ha₀, hmax⟩ := ZeroSumPositiveMaximum.zeroSum_nonzero_exists_positive_maximum a ha hne
  have hdim : Module.finrank K (Fin r → K) = r := by simp
  obtain ⟨κ, hκ, b, σ, hb, hsum⟩ := SparsePositiveWeightBasis.sparseFamily_positiveWeightBasis v
    (hdim.symm ▸ hr) (by simpa only [hdim, Fintype.card_fin] using hs)
    a ha i₀ (hv i₀) ha₀ hmax
  let : Fintype κ := hκ
  have hcard : Fintype.card κ = r := (Module.finrank_eq_card_basis b).symm.trans hdim
  let e : Fin r ≃ κ := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hcard.symm)
  let b' : Module.Basis (Fin r) K (Fin r → K) := b.reindex e.symm
  have hb' : (fun j => v (σ (e j))) = b' := by
    funext j
    simpa only [b', Module.Basis.reindex_apply, Equiv.symm_symm] using hb (e j)
  refine ⟨fun j => σ (e j), ?_, ?_⟩
  · rw [LabeledDeterminantPolynomials.labeledDeterminant_eq_basis, hb']
    exact ((Pi.basisFun K (Fin r)).isUnit_det b').ne_zero
  · rw [e.sum_comp (fun j => a (σ j))]
    exact hsum

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SparseDeterminantSeparation
