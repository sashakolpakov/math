import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Pi.Lemmas

/-! # Padic -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Padic.Construction

noncomputable section

/-!
Compute the actual additive quotient of a q-adic coordinate lattice by
its diagonal q-powers. The quotient is the prescribed product of Z/(q^a),
using the genuine residue maps and their proved kernels.
-/

variable (q : ℕ) [Fact q.Prime] {d : ℕ}

def padicCoordinateResidues (a : Fin d → ℕ) :
    (Fin d → ℤ_[q]) →+ (∀ i, ZMod (q ^ a i)) where
  toFun x i := PadicInt.toZModPow (a i) (x i)
  map_zero' := funext (fun _ => map_zero _)
  map_add' x y := funext (fun i => map_add _ (x i) (y i))

theorem padicCoordinateResidues_surjective (a : Fin d → ℕ) :
    Function.Surjective (padicCoordinateResidues q a) := by
  intro x
  choose r hr using fun i => ZMod.ringHom_surjective (PadicInt.toZModPow (p := q) (a i)) (x i)
  exact ⟨r, funext hr⟩

def padicDiagonalSubgroup (a : Fin d → ℕ) : AddSubgroup (Fin d → ℤ_[q]) where
  carrier := {x | ∀ i, x i ∈ Ideal.span {(q : ℤ_[q]) ^ a i}}
  zero_mem' i := (Ideal.span {(q : ℤ_[q]) ^ a i}).zero_mem
  add_mem' hx hy i := (Ideal.span {(q : ℤ_[q]) ^ a i}).add_mem (hx i) (hy i)
  neg_mem' hx i := (Ideal.span {(q : ℤ_[q]) ^ a i}).neg_mem (hx i)

/-- The coordinate residue map has exactly the diagonal q-power subgroup as kernel. -/
theorem padicCoordinateResidues_ker (a : Fin d → ℕ) :
    (padicCoordinateResidues q a).ker = padicDiagonalSubgroup q a := by
  ext x
  change (fun i => PadicInt.toZModPow (a i) (x i)) = 0 ↔
    ∀ i, x i ∈ Ideal.span {(q : ℤ_[q]) ^ a i}
  rw [funext_iff]
  apply forall_congr'
  intro i
  rw [← PadicInt.ker_toZModPow]
  rfl

/-- An actual quotient-group isomorphism, not merely an equality of cardinalities. -/
def padicDiagonalQuotientEquiv (a : Fin d → ℕ) :
    (Fin d → ℤ_[q]) ⧸ padicDiagonalSubgroup q a ≃+ (∀ i, ZMod (q ^ a i)) :=
  (QuotientAddGroup.quotientAddEquivOfEq (padicCoordinateResidues_ker q a).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (padicCoordinateResidues q a)
      (padicCoordinateResidues_surjective q a))

theorem padicDiagonalQuotient_finite (a : Fin d → ℕ) :
    Finite ((Fin d → ℤ_[q]) ⧸ padicDiagonalSubgroup q a) := by
  exact Finite.of_equiv (∀ i, ZMod (q ^ a i)) (padicDiagonalQuotientEquiv q a).symm.toEquiv

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Padic.Construction
