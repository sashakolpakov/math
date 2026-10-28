import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LabeledDeterminantPolynomials
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Labeled Determinant Span Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LabeledDeterminantSpanCriterion

noncomputable section

/-! A labeled family spans exactly when one of its maximal minors is
nonzero. The selected labels may be restricted to any prescribed subset. -/
open scoped Classical
universe u
variable {K : Type u} [Field K] {r m : ℕ}

theorem spanningLabels_exists_nonzero_determinant (v : Fin m → Fin r → K) (H : Set (Fin m))
    (hspan : Submodule.span K (v '' H) = ⊤) :
    ∃ σ : Fin r → Fin m, (∀ j, σ j ∈ H) ∧ LabeledDeterminantPolynomials.labeledDeterminant σ v ≠ 0 := by
  have hli : LinearIndepOn K id (∅ : Set (Fin r → K)) := by simp
  have hsub : (∅ : Set (Fin r → K)) ⊆ v '' H := Set.empty_subset _
  let κ := hli.extend hsub
  let b : Module.Basis κ K (Fin r → K) := Module.Basis.extendLe hli hsub hspan.ge
  let : Finite κ := Module.Finite.finite_basis b
  let : Fintype κ := Fintype.ofFinite κ
  have hc : Fintype.card κ = r := by
    rw [← Module.finrank_eq_card_basis b]
    exact Module.finrank_fin_fun K
  let q : κ ≃ Fin r := (Fintype.equivFin κ).trans (finCongr hc)
  let b' := b.reindex q
  have hb (j : Fin r) : ∃ i ∈ H, v i = b' j := by
    have hmem : b (q.symm j) ∈ v '' H :=
      Module.Basis.extendLe_subset hli hsub hspan.ge ⟨q.symm j, rfl⟩
    obtain ⟨i, hi, hbi⟩ := hmem
    refine ⟨i, hi, ?_⟩
    simpa only [b', Module.Basis.reindex_apply] using hbi
  choose σ hσ hv using hb
  refine ⟨σ, hσ, ?_⟩
  rw [LabeledDeterminantPolynomials.labeledDeterminant_eq_basis]
  have he : (fun j => v (σ j)) = b' := funext hv
  rw [he]
  exact ((Pi.basisFun K (Fin r)).isUnit_det b').ne_zero

theorem labeledDeterminant_eq_zero_of_mem_proper_submodule (v : Fin m → Fin r → K)
    (W : Submodule K (Fin r → K)) (hW : W ≠ ⊤) (σ : Fin r → Fin m)
    (hσ : ∀ j, v (σ j) ∈ W) : LabeledDeterminantPolynomials.labeledDeterminant σ v = 0 := by
  by_contra hd
  have hu : IsUnit ((Pi.basisFun K (Fin r)).det (fun j => v (σ j))) :=
    isUnit_iff_ne_zero.mpr ((LabeledDeterminantPolynomials.labeledDeterminant_eq_basis σ v) ▸ hd)
  have ht := ((Pi.basisFun K (Fin r)).is_basis_iff_det.mpr hu).2
  have hle : Submodule.span K (Set.range (fun j => v (σ j))) ≤ W :=
    Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hσ j)
  exact hW (top_unique (ht ▸ hle))

theorem labeledSpan_ne_top_of_all_determinants_zero (v : Fin m → Fin r → K)
    (H : Set (Fin m)) (h : ∀ σ : Fin r → Fin m,
      (∀ j, σ j ∈ H) → LabeledDeterminantPolynomials.labeledDeterminant σ v = 0) :
    Submodule.span K (v '' H) ≠ ⊤ := by
  intro htop
  obtain ⟨σ, hσ, hd⟩ := spanningLabels_exists_nonzero_determinant v H htop
  exact hd (h σ hσ)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LabeledDeterminantSpanCriterion
