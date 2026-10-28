import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! # Transported Invariant Complement -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.TransportedInvariantComplement.Construction

noncomputable section

/-! A family symmetric for a transported positive inner product has
a common invariant complement to every common invariant subspace. -/

open scoped RealInnerProductSpace

theorem exists_invariant_complement_of_transported_symmetry
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (Φ : E ≃L[ℝ] F) (U : Submodule ℝ E) (T : ι → E →L[ℝ] E)
    (hT : ∀ i x y, inner ℝ (Φ (T i x)) (Φ y) = inner ℝ (Φ x) (Φ (T i y)))
    (hU : ∀ i x, x ∈ U → T i x ∈ U) :
    ∃ V : Submodule ℝ E, IsCompl V U ∧ ∀ i x, x ∈ V → T i x ∈ V := by
  let o := Submodule.orderIsoMapComap Φ.toLinearEquiv
  let Q := U.map Φ.toLinearMap
  let V := o.symm Qᗮ
  have hcompl : IsCompl U V := by
    apply o.isCompl_iff.mpr
    change IsCompl Q (o (o.symm Qᗮ))
    rw [o.apply_symm_apply]
    exact Q.isCompl_orthogonal
  refine ⟨V, hcompl.symm, ?_⟩
  intro i x hx
  change Φ x ∈ Qᗮ at hx
  change Φ (T i x) ∈ Qᗮ
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  change inner ℝ (Φ z) (Φ (T i x)) = 0
  rw [← hT i z x]
  exact hx (Φ (T i z)) (Submodule.mem_map_of_mem (hU i z hz))

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.TransportedInvariantComplement.Construction
