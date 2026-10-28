import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Separating Covectors Span -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SeparatingCovectorsSpan.LinearAlgebra

noncomputable section

/-! A separating family of covectors spans the dual of a finite-dimensional vector space. -/

variable {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem covectors_span_of_separating (f : ι → Module.Dual K V)
    (hf : ∀ v, (∀ i, f i v = 0) → v = 0) : Submodule.span K (Set.range f) = ⊤ := by
  have h : (Submodule.span K (Set.range f)).dualCoannihilator = ⊥ := by
    apply bot_unique
    intro v hv
    change v = 0
    apply hf v
    intro i
    exact (Submodule.mem_dualCoannihilator v).mp hv (f i) (Submodule.subset_span ⟨i, rfl⟩)
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span K (Set.range f)),
    h, Submodule.dualAnnihilator_bot]

end

end OAI.AlgebraicGeometry.Comparison.Betti.SeparatingCovectorsSpan.LinearAlgebra
