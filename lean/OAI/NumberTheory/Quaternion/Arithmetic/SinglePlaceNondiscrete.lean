import OAI.NumberTheory.Quaternion.Arithmetic.Ambient
import OAI.NumberTheory.Quaternion.Arithmetic.Closure

/-! # Single Place Nondiscrete -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.SinglePlaceNondiscrete

noncomputable section

/-! The quotient-volume argument gives nondiscreteness of the actual
single-place S-integral arithmetic image. -/

open scoped Classical
open Set

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem arithmeticSubgroup_singleton (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Finset (LocalAdeles.Place F)) (w : ApproximationTopology.AwayPlace S) :
    Groups.arithmeticSubgroup G S {w} = Groups.sIntegralPoints G (↑(insert w.val S)) := by
  rw [Groups.arithmeticSubgroup_eq_sIntegralPoints]
  simp only [Finset.coe_singleton, image_singleton, union_singleton, Finset.coe_insert]

def singleSelectedHomeomorph (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Finset (LocalAdeles.Place F)) (w : ApproximationTopology.AwayPlace S) :
    Groups.SelectedLocalProduct G S {w} ≃ₜ LocalAdeles.LocalPoints G w.val := by
  let I := {a : ApproximationTopology.AwayPlace S // a ∈ ({w} : Finset (ApproximationTopology.AwayPlace S))}
  let : Unique I := {
    default := ⟨w, Finset.mem_singleton_self w⟩
    uniq := fun a => Subtype.ext (Finset.mem_singleton.mp a.property) }
  exact Homeomorph.piUnique (fun a : I => LocalAdeles.LocalPoints G a.val.val)

theorem localArithmetic_single_not_discrete (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Finset (LocalAdeles.Place F)) (w : ApproximationTopology.AwayPlace S)
    (hnoncompact : ∃ v : LocalAdeles.Place F, v ∈ S ∧ ¬ CompactSpace (LocalAdeles.LocalPoints G v))
    (hvolume : CompactQuotientProjection.QuotientHasInvariantProbability (Ambient.arithmeticAmbientSubgroup G S {w})) :
    ¬ IsDiscrete (Closure.localArithmeticSubgroup G (insert w.val S) w.val : Set (LocalAdeles.LocalPoints G w.val)) := by
  intro hd
  apply Ambient.arithmeticProjection_not_discrete G S {w} (Finset.singleton_nonempty w) hnoncompact hvolume
  let e := singleSelectedHomeomorph G S w
  apply (hd.preimage e.continuous.continuousOn e.injective).mono
  rintro x ⟨g, rfl⟩
  change LocalAdeles.diagonalLocal G w.val g.val ∈ Closure.localArithmeticSubgroup G (insert w.val S) w.val
  refine ⟨g.val, ?_, rfl⟩
  exact (arithmeticSubgroup_singleton G S w).le g.property

end

end OAI.NumberTheory.Quaternion.Arithmetic.SinglePlaceNondiscrete
