import Mathlib.Algebra.Lie.Semisimple.Basic

/-! # Algebra -/

namespace OAI.LieTheory.Semisimple.Algebra.Constructions.CharacterTriviality

/-! Algebraic support for CharacterTriviality: a semisimple Lie algebra is spanned by brackets. -/

open LieAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieAlgebra.IsSemisimple R L]

theorem bracket_self_eq_of_atom (I : LieIdeal R L) (hI : IsAtom I) : ⁅I, I⁆ = I := by
  apply (hI.le_iff_eq ?_).mp (LieSubmodule.lie_le_left I I)
  intro hz
  apply LieAlgebra.IsSemisimple.non_abelian_of_isAtom I hI
  constructor
  intro x y
  apply Subtype.ext
  exact (LieSubmodule.lie_eq_bot_iff I I).mp hz x x.property y y.property

theorem bracket_top_eq_top : ⁅(⊤ : LieIdeal R L), (⊤ : LieIdeal R L)⁆ = ⊤ := by
  apply top_unique
  conv_lhs => rw [← LieAlgebra.IsSemisimple.sSup_atoms_eq_top (R := R) (L := L)]
  apply sSup_le
  intro I hI
  rw [← bracket_self_eq_of_atom I hI]
  exact LieSubmodule.mono_lie le_top le_top

theorem linearMap_eq_zero_of_brackets
    {V : Type*} [AddCommGroup V] [Module R V]
    (f : L →ₗ[R] V) (hf : ∀ x y : L, f ⁅x, y⁆ = 0) : f = 0 := by
  apply LinearMap.ker_eq_top.mp
  apply top_unique
  have h := congrArg LieSubmodule.toSubmodule (bracket_top_eq_top (R := R) (L := L))
  rw [LieSubmodule.lieIdeal_oper_eq_linear_span] at h
  change _ = (⊤ : Submodule R L) at h
  rw [← h]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, y, rfl⟩
  exact hf x y

end OAI.LieTheory.Semisimple.Algebra.Constructions.CharacterTriviality
