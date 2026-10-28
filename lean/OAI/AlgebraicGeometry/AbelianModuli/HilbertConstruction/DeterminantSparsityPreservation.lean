import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LabeledDeterminantSpanCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.MonomialAlgebra

/-! # Determinant Sparsity Preservation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DeterminantSparsityPreservation

noncomputable section

/-! Preserving the nonzero maximal minors preserves the hyperplane
sparsity inequality. A monomial positive on every original nonzero minor
therefore defines an open neighborhood consisting entirely of sparse points. -/
open scoped BigOperators Classical
universe u v
variable {K : Type u} [Field K] {L : Type v} [Field L] {r m : ℕ}

theorem hyperplaneSparsity_of_nonzero_minors_preserved
    (v : Fin m → Fin r → K) (w : Fin m → Fin r → L)
    (hs : ∀ W : Submodule K (Fin r → K), W ≠ ⊤ →
      r * (Finset.univ.filter (fun i => v i ∈ W)).card < m)
    (hminor : ∀ σ : Fin r → Fin m, LabeledDeterminantPolynomials.labeledDeterminant σ v ≠ 0 → LabeledDeterminantPolynomials.labeledDeterminant σ w ≠ 0) :
    ∀ W : Submodule L (Fin r → L), W ≠ ⊤ →
      r * (Finset.univ.filter (fun i => w i ∈ W)).card < m := by
  intro W hW
  let H : Set (Fin m) := {i | w i ∈ W}
  let V := Submodule.span K (v '' H)
  have hV : V ≠ ⊤ := by
    apply LabeledDeterminantSpanCriterion.labeledSpan_ne_top_of_all_determinants_zero v H
    intro σ hσ
    by_contra hd
    exact hminor σ hd (LabeledDeterminantSpanCriterion.labeledDeterminant_eq_zero_of_mem_proper_submodule w W hW σ hσ)
  have hsub : Finset.univ.filter (fun i => w i ∈ W) ⊆
      Finset.univ.filter (fun i => v i ∈ V) := by
    intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Submodule.subset_span ?_⟩
    exact ⟨i, (Finset.mem_filter.mp hi).2, rfl⟩
  exact (Nat.mul_le_mul_left r (Finset.card_le_card hsub)).trans_lt (hs V hV)

theorem hyperplaneSparsity_of_nonvanishing_determinant_monomial
    (v : Fin m → Fin r → K) (w : Fin m → Fin r → L)
    (a : (Fin r → Fin m) → ℕ)
    (ha : ∀ σ, LabeledDeterminantPolynomials.labeledDeterminant σ v ≠ 0 → 0 < a σ)
    (hw : Balanced.MonomialAlgebra.exponentMonomial (fun σ => LabeledDeterminantPolynomials.labeledDeterminant σ w) a ≠ 0)
    (hs : ∀ W : Submodule K (Fin r → K), W ≠ ⊤ →
      r * (Finset.univ.filter (fun i => v i ∈ W)).card < m) :
    ∀ W : Submodule L (Fin r → L), W ≠ ⊤ →
      r * (Finset.univ.filter (fun i => w i ∈ W)).card < m := by
  apply hyperplaneSparsity_of_nonzero_minors_preserved v w hs
  intro σ hσ hd
  have hf : LabeledDeterminantPolynomials.labeledDeterminant σ w ^ a σ ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hw σ (Finset.mem_univ σ)
  exact hf (by rw [hd, zero_pow (Nat.ne_of_gt (ha σ hσ))])

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DeterminantSparsityPreservation
