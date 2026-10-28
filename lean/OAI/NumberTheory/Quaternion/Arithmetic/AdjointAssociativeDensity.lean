import OAI.NumberTheory.Quaternion.Arithmetic.IrreducibleDensity
import OAI.NumberTheory.Quaternion.Arithmetic.LieScalarSimplicity
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! # Adjoint Associative Density -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.AdjointAssociativeDensity

noncomputable section

/-! Over an algebraically closed field, the associative algebra generated
by the adjoint operators of a simple finite-dimensional Lie algebra is
the full endomorphism algebra. -/

open scoped Classical

variable (k L : Type*) [Field k] [LieRing L] [LieAlgebra k L]

def adjointAssociativeAlgebra : Subalgebra k (Module.End k L) :=
  Algebra.adjoin k (Set.range (LieModule.toEnd k L L))

theorem adjointAssociativeAlgebra_simpleModule [LieAlgebra.IsSimple k L] :
    IsSimpleModule (adjointAssociativeAlgebra k L) L := by
  let R := adjointAssociativeAlgebra k L
  let : Nontrivial L := LieAlgebra.IsSimple.nontrivial k L
  have hs : IsSimpleOrder (Submodule R L) :=
    { toNontrivial := inferInstance
      eq_bot_or_eq_top := by
        intro N
        let I : LieIdeal k L :=
          { N.restrictScalars k with
            lie_mem := by
              intro x y hy
              exact N.smul_mem
                (⟨LieModule.toEnd k L L x, Algebra.subset_adjoin (Set.mem_range_self x)⟩ : R) hy }
        rcases LieAlgebra.IsSimple.eq_bot_or_eq_top I with hI | hI
        · left
          apply le_antisymm _ bot_le
          intro x hx
          have hm : x ∈ I := hx
          rwa [hI, LieSubmodule.mem_bot] at hm
        · right
          apply le_antisymm le_top
          intro x _
          have hm : x ∈ I := by rw [hI]; trivial
          exact hm }
  exact { toIsSimpleOrder := hs }

theorem adjointAssociativeAlgebra_eq_top
    [IsAlgClosed k] [FiniteDimensional k L] [LieAlgebra.IsSimple k L] :
    adjointAssociativeAlgebra k L = ⊤ := by
  let R := adjointAssociativeAlgebra k L
  let : IsSimpleModule R L := adjointAssociativeAlgebra_simpleModule k L
  apply top_unique
  intro φ _
  obtain ⟨r, hr⟩ := IrreducibleDensity.irreducible_algebra_action_surjective (k := k) (R := R) (V := L) φ
  have he : r.val = φ := hr
  exact he ▸ r.property

end

end OAI.NumberTheory.Quaternion.Arithmetic.AdjointAssociativeDensity
