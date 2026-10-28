import OAI.NumberTheory.Quaternion.Arithmetic.LieScalarSimplicity
import Mathlib.Order.CompactlyGenerated.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Finite Lie Ideals -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.FiniteLieIdeals

noncomputable section

/-! A finite-dimensional semisimple Lie algebra has finitely many ideals.
Each ideal is determined by the simple factors it contains. This supports
the connected algebraic group's action on its Lie ideals. -/

open scoped Classical
open Set

theorem finite_lieIdeals_of_semisimple
    (K L : Type*) [Field K] [LieRing L] [LieAlgebra K L]
    [FiniteDimensional K L] [LieAlgebra.IsSemisimple K L] : Finite (LieIdeal K L) := by
  let S : Set (LieIdeal K L) := {I | IsAtom I}
  have hS : S.Finite := WellFoundedGT.finite_of_sSupIndep
    (LieAlgebra.IsSemisimple.sSupIndep_isAtom (R := K) (L := L))
  let : Finite S := hS.to_subtype
  let : IsAtomistic (LieIdeal K L) :=
    (LieAlgebra.IsSemisimple.booleanGenerators K L).isAtomistic_of_sSup_eq_top
      LieAlgebra.IsSemisimple.sSup_atoms_eq_top
  let f : LieIdeal K L → Set S := fun I => {J | J.val ≤ I}
  apply Finite.of_injective f
  intro I J hIJ
  have he : {a : LieIdeal K L | IsAtom a ∧ a ≤ I} = {a | IsAtom a ∧ a ≤ J} := by
    ext a
    constructor
    · rintro ⟨ha, hle⟩
      refine ⟨ha, ?_⟩
      have hm : (⟨a, ha⟩ : S) ∈ f I := hle
      rwa [hIJ] at hm
    · rintro ⟨ha, hle⟩
      refine ⟨ha, ?_⟩
      have hm : (⟨a, ha⟩ : S) ∈ f J := hle
      rwa [← hIJ] at hm
  calc
    I = sSup {a : LieIdeal K L | IsAtom a ∧ a ≤ I} := (sSup_atoms_le_eq I).symm
    _ = sSup {a : LieIdeal K L | IsAtom a ∧ a ≤ J} := congrArg sSup he
    _ = J := sSup_atoms_le_eq J

end

end OAI.NumberTheory.Quaternion.Arithmetic.FiniteLieIdeals
