import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SubquotientCharacterRank
import Mathlib.Data.ZMod.Basic

/-! # Finite Subquotient Character Rank -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteSubquotientCharacterRank.Construction

noncomputable section

/-! Every subquotient of d cyclic groups has at most d independent
additive characters over a field. No choice of cyclic generators for
the subgroup or its quotient is an assumption. -/

theorem subgroupQuotientCharacter_finrank_le
    {k G Q : Type*} [Field k] [AddCommGroup G] [AddCommGroup Q] {d : ℕ}
    (r : (Fin d → ℤ) →+ G) (hr : Function.Surjective r)
    (H : AddSubgroup G) (p : H →+ Q) (hp : Function.Surjective p) :
    Module.finrank k (Q →+ k) ≤ d := by
  let S := (H.comap r).toIntSubmodule
  let t : S →+ H := {
    toFun x := ⟨r x.val, x.property⟩
    map_zero' := Subtype.ext r.map_zero
    map_add' x y := Subtype.ext (r.map_add x.val y.val) }
  apply SubquotientCharacterRank.Construction.subquotientCharacter_finrank_le S (p.comp t)
  intro x
  obtain ⟨y, rfl⟩ := hp x
  obtain ⟨z, hz⟩ := hr y.val
  have hzH : r z ∈ H := hz.symm ▸ y.property
  refine ⟨⟨z, hzH⟩, ?_⟩
  exact congrArg p (Subtype.ext hz)

def integerCyclicCoordinates (m d : ℕ) : (Fin d → ℤ) →+ (Fin d → ZMod m) where
  toFun x i := (x i : ZMod m)
  map_zero' := funext fun _ => Int.cast_zero
  map_add' x y := funext fun i => Int.cast_add (x i) (y i)

theorem integerCyclicCoordinates_surjective (m d : ℕ) :
    Function.Surjective (integerCyclicCoordinates m d) := by
  intro x
  choose y hy using fun i => ZMod.intCast_surjective (x i)
  exact ⟨y, funext hy⟩

theorem finiteCyclicSubquotientCharacter_finrank_le
    {k Q : Type*} [Field k] [AddCommGroup Q] (m d : ℕ)
    (H : AddSubgroup (Fin d → ZMod m)) (p : H →+ Q) (hp : Function.Surjective p) :
    Module.finrank k (Q →+ k) ≤ d :=
  subgroupQuotientCharacter_finrank_le (integerCyclicCoordinates m d)
    (integerCyclicCoordinates_surjective m d) H p hp

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteSubquotientCharacterRank.Construction
