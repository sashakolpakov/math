import OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentBracketGroup

/-! # Orthogonal Bracket Unit Compactness -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalBracketUnitCompactness.Construction

noncomputable section

/-! The compact orthogonal bracket operators form a compact subgroup
of the topological group of invertible continuous endomorphisms. -/

open _root_.ContinuousLinearMap Set

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem orthogonalBracketUnit_adjoint_eq_inv
    (B : L →L[ℝ] L →L[ℝ] L) (g : (L →L[ℝ] L)ˣ)
    (hg : (g : L →L[ℝ] L) ∈ OrthogonalBracketCompactness.Construction.orthogonalBracketOperators B) :
    adjoint (g : L →L[ℝ] L) = (↑g⁻¹ : L →L[ℝ] L) := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  have he : OrthogonalBracketAlgebra.Construction.orthogonalBracketEquiv B (g : L →L[ℝ] L) hg = ContinuousLinearEquiv.ofUnit g := by
    ext x
    rfl
  rw [OrthogonalBracketAlgebra.Construction.orthogonalBracketEquiv_adjoint B (g : L →L[ℝ] L) hg, he]
  rfl

def orthogonalBracketUnitGroup (B : L →L[ℝ] L →L[ℝ] L) : Subgroup (L →L[ℝ] L)ˣ where
  carrier := {g | (g : L →L[ℝ] L) ∈ OrthogonalBracketCompactness.Construction.orthogonalBracketOperators B}
  one_mem' := OrthogonalBracketAlgebra.Construction.orthogonalBracketOperators_one B
  mul_mem' := OrthogonalBracketAlgebra.Construction.orthogonalBracketOperators_mul B
  inv_mem' {g} hg := by
    let : CompleteSpace L := FiniteDimensional.complete ℝ L
    change (↑g⁻¹ : L →L[ℝ] L) ∈ OrthogonalBracketCompactness.Construction.orthogonalBracketOperators B
    rw [← orthogonalBracketUnit_adjoint_eq_inv B g hg]
    exact OrthogonalBracketAlgebra.Construction.orthogonalBracketOperators_adjoint B hg

theorem orthogonalBracketUnitGroup_isCompact (B : L →L[ℝ] L →L[ℝ] L) :
    IsCompact (orthogonalBracketUnitGroup B : Set (L →L[ℝ] L)ˣ) := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  let K := OrthogonalBracketCompactness.Construction.orthogonalBracketOperators B
  let : CompactSpace K := (isCompact_iff_compactSpace).mp (OrthogonalBracketCompactness.Construction.orthogonalBracketOperators_isCompact B)
  let f : K → (L →L[ℝ] L)ˣ := fun T => (OrthogonalBracketAlgebra.Construction.orthogonalBracketEquiv B T.val T.property).toUnit
  have hf : Continuous f := by
    apply Units.continuous_iff.mpr
    constructor
    · exact continuous_subtype_val
    · have he : (fun T : K => (↑(f T)⁻¹ : L →L[ℝ] L)) = fun T : K => adjoint T.val := by
        funext T
        exact (OrthogonalBracketAlgebra.Construction.orthogonalBracketEquiv_adjoint B T.val T.property).symm
      rw [he]
      exact adjoint.continuous.comp continuous_subtype_val
  have himage : f '' Set.univ = (orthogonalBracketUnitGroup B : Set (L →L[ℝ] L)ˣ) := by
    ext g
    constructor
    · rintro ⟨T, _, rfl⟩
      exact T.property
    · intro hg
      refine ⟨⟨(g : L →L[ℝ] L), hg⟩, Set.mem_univ _, ?_⟩
      apply Units.ext
      rfl
  rw [← himage]
  exact isCompact_univ.image hf

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalBracketUnitCompactness.Construction
