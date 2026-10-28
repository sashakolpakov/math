import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Spanning Family Basis -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SpanningFamilyBasis.LinearAlgebra

noncomputable section

/-! A spanning family contains a basis with its original family labels retained. -/

variable {K V α : Type} [Field K] [AddCommGroup V] [Module K V]

theorem exists_basis_subfamily_of_span (f : α → V) (hf : Submodule.span K (Set.range f) = ⊤) :
    ∃ (s : Set V) (b : Module.Basis s K V) (a : s → α), ∀ i, b i = f (a i) := by
  let h : ⊤ ≤ Submodule.span K (Set.range f) := hf.ge
  let s := (linearIndepOn_empty K (id : V → V)).extend (Set.empty_subset (Set.range f))
  let b : Module.Basis s K V := Module.Basis.ofSpan h
  have hb : Set.range b ⊆ Set.range f := Module.Basis.ofSpan_subset h
  have hi (i : s) : ∃ a, f a = b i := hb ⟨i, rfl⟩
  choose a ha using hi
  exact ⟨s, b, a, fun i => (ha i).symm⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.SpanningFamilyBasis.LinearAlgebra
