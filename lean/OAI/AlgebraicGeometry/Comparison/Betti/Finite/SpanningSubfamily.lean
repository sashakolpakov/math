import OAI.AlgebraicGeometry.Comparison.Betti.SpanningFamilyBasis
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Spanning Subfamily -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Finite.SpanningSubfamily.LinearAlgebra

noncomputable section

/-! A finite-dimensional spanning family supplies a finite basis with its original labels. -/

variable {K V α : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_fin_basis_subfamily (f : α → V) (hf : Submodule.span K (Set.range f) = ⊤) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) K V) (a : Fin n → α), ∀ i, b i = f (a i) := by
  obtain ⟨s, b, a, ha⟩ := SpanningFamilyBasis.LinearAlgebra.exists_basis_subfamily_of_span f hf
  let : Fintype s := FiniteDimensional.fintypeBasisIndex b
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  refine ⟨Fintype.card s, b.reindex e, a ∘ e.symm, ?_⟩
  intro i
  simpa using ha (e.symm i)

theorem exists_fin_basis_subfamily_of_span_eq
    (W : Submodule K V) (f : α → V) (hf : Submodule.span K (Set.range f) = W) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) K W) (a : Fin n → α),
      ∀ i, (b i : V) = f (a i) := by
  have hmem (a : α) : f a ∈ W := hf ▸ Submodule.subset_span ⟨a, rfl⟩
  have hspan := (Submodule.span_range_subtype_eq_top_iff W hmem).mpr hf
  obtain ⟨n, b, a, ha⟩ := exists_fin_basis_subfamily (fun a => (⟨f a, hmem a⟩ : W)) hspan
  exact ⟨n, b, a, fun i => congrArg Subtype.val (ha i)⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Finite.SpanningSubfamily.LinearAlgebra
