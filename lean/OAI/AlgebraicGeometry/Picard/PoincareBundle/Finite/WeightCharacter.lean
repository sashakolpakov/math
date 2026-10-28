import OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.CoalgebraGroupLike
import Mathlib.RingTheory.HopfAlgebra.GroupLike

/-! # Weight Character -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.WeightCharacter

noncomputable section

/-! A nonzero finite weight coalgebra supplies an actual invertible Hopf character with the prescribed restriction. -/

universe u v w w'

open Coalgebra

variable (k : Type u) [Field k] [IsAlgClosed k]
  (C : Type v) [AddCommGroup C] [Module k C] [Module.Finite k C] [Nontrivial C]
  [Coalgebra k C] [Coalgebra.IsCocomm k C]
  (H : Type w) [CommRing H] [HopfAlgebra k H]
  (j : C →ₗc[k] H)
  (R : Type w') [CommRing R] [Algebra k R] (r : H →ₐ[k] R) (χ : Rˣ)

/-- A finite nonzero weight space contains a group-like unit whose restriction is the desired character. -/
theorem exists_character
    (hw : ∀ c : C, r (j c) = counit (R := k) c • χ.val) :
    ∃ z : Hˣ, IsGroupLikeElem k z.val ∧ Units.map r.toMonoidHom z = χ := by
  obtain ⟨c, hc⟩ := CoalgebraGroupLike.exists_groupLike k C
  have hj : IsGroupLikeElem k (j c) := hc.map j
  let z : Hˣ := GroupLike.toUnits k ⟨j c, hj⟩
  refine ⟨z, hj, ?_⟩
  apply Units.ext
  change r (j c) = χ.val
  rw [hw, hc.counit_eq_one, one_smul]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.WeightCharacter
