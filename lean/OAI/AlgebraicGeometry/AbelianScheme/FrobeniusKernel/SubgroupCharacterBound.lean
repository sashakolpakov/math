import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteSubquotientCharacterRank
import Mathlib.Algebra.Group.Subgroup.Ker

/-! # Subgroup Character Bound -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SubgroupCharacterBound.Construction

noncomputable section

/-! Characters of a subgroup of a quotient of a rank-d lattice have
at most d independent values, with the subgroup given by an actual injection. -/

theorem subgroupCharacter_finrank_le_of_injective
    {k G Q : Type*} [Field k] [AddCommGroup G] [AddCommGroup Q] {d : ℕ}
    (r : (Fin d → ℤ) →+ G) (hr : Function.Surjective r)
    (i : Q →+ G) (hi : Function.Injective i) :
    Module.finrank k (Q →+ k) ≤ d := by
  let e := AddMonoidHom.ofInjective hi
  exact FiniteSubquotientCharacterRank.Construction.subgroupQuotientCharacter_finrank_le r hr i.range e.symm.toAddMonoidHom e.symm.surjective

theorem finiteCyclicSubgroupCharacter_finrank_le
    {k G Q : Type*} [Field k] [AddCommGroup G] [AddCommGroup Q] (m d : ℕ)
    (r : (Fin d → ZMod m) →+ G) (hr : Function.Surjective r)
    (i : Q →+ G) (hi : Function.Injective i) :
    Module.finrank k (Q →+ k) ≤ d :=
  subgroupCharacter_finrank_le_of_injective (r.comp (FiniteSubquotientCharacterRank.Construction.integerCyclicCoordinates m d))
    (hr.comp (FiniteSubquotientCharacterRank.Construction.integerCyclicCoordinates_surjective m d)) i hi

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SubgroupCharacterBound.Construction
