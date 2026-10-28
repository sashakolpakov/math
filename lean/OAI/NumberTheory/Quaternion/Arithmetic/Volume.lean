import OAI.NumberTheory.Quaternion.Arithmetic.Discrete
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.QuotientLattice

/-! # Volume -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.Volume

noncomputable section

/-! The invariant volume of S-arithmetic quotients follows from a
compact full adelic quotient and the proved arithmetic discreteness. -/

open scoped Classical
open OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.QuotientLattice.Construction _root_.NumberField

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem sArithmeticLocal_quotientProbability_of_full (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
    (harch : ∀ v : InfinitePlace F, Sum.inl v ∈ S)
    [CompactSpace (AdelicGroup.FullAdelicGroupPoints G ⧸ (AdelicGroup.diagonalFullAdelic G).range)] :
    CompactQuotientProjection.QuotientHasInvariantProbability (Adelic.sArithmeticLocalSubgroup G S) := by
  let : DiscreteTopology (Adelic.sArithmeticLocalSubgroup G S) := Discrete.sArithmeticLocalSubgroup_discrete G S harch
  let : CompactSpace (Ambient.OmittedLocalProduct G S ⧸ Adelic.sArithmeticLocalSubgroup G S) :=
    Adelic.compact_sArithmeticLocal_quotient_of_full G S
  exact (ArithmeticGroups.Lattices.Compact.QuotientLattice.Construction.lattice_of_discrete_compact_quotient (Adelic.sArithmeticLocalSubgroup G S)).2

end

end OAI.NumberTheory.Quaternion.Arithmetic.Volume
