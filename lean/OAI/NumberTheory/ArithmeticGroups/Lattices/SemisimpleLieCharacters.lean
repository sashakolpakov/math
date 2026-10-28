import Mathlib

/-! # Semisimple Lie Characters -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.SemisimpleLieCharacters.Construction

noncomputable section

/-! Semisimple Lie algebras are perfect and have no nonzero homomorphisms
to abelian Lie algebras. -/

open scoped Classical

theorem semisimpleLie_derived_eq_top
    {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieAlgebra.IsSemisimple R L] : LieAlgebra.derivedSeries R L 1 = ⊤ := by
  apply top_unique
  rw [← LieAlgebra.IsSemisimple.sSup_atoms_eq_top (R := R) (L := L)]
  apply sSup_le
  intro I hI
  have hne : LieAlgebra.derivedSeriesOfIdeal R L 1 I ≠ ⊥ := by
    intro h
    exact LieAlgebra.IsSemisimple.non_abelian_of_isAtom I hI
      ((LieAlgebra.abelian_iff_derived_one_eq_bot I).mpr h)
  have he : LieAlgebra.derivedSeriesOfIdeal R L 1 I = I :=
    (hI.le_iff_eq hne).mp (LieAlgebra.derivedSeriesOfIdeal_le_self I 1)
  rw [← he]
  exact LieAlgebra.derivedSeriesOfIdeal_mono le_top 1

theorem semisimpleLie_hom_to_abelian_eq_zero
    {R L A : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieAlgebra.IsSemisimple R L] [LieRing A] [LieAlgebra R A] [IsLieAbelian A]
    (f : L →ₗ⁅R⁆ A) : f = 0 := by
  have hker : (LieAlgebra.derivedSeries R L 1 : Submodule R L) ≤ (f.ker : Submodule R L) := by
    rw [LieAlgebra.coe_derivedSeries_one_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, y, rfl⟩
    change f ⁅x, y⁆ = 0
    rw [f.map_lie]
    exact LieModule.IsTrivial.trivial _ _
  rw [semisimpleLie_derived_eq_top] at hker
  ext x
  exact hker (Submodule.mem_top : x ∈ (⊤ : Submodule R L))

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.SemisimpleLieCharacters.Construction
