import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramHash
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel

namespace OAI.Algorithms

/-! Integer representative lifting of the ternary selector coefficients.
Only reduction is a ring homomorphism. The lift itself is a finite choice of
0, 1, or 2, and no ring homomorphism from `ZMod 3` into the thickened ring is
assumed. All statements use the supplied irreducible polynomial. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram

section Naturality
variable {V C R S : Type*} [CommRing R] [CommRing S]

theorem map_literalValue (rho : R →+* S) (value : V → R) (l : SAT.Literal V) :
    rho (literalValue (ringAlgebra R) value l) =
      literalValue (ringAlgebra S) (fun v => rho (value v)) l := by
  cases hp : l.positive <;> simp [literalValue, ringAlgebra, hp]

theorem map_clauseValue (rho : R →+* S) (value : V → R) (ls : List (SAT.Literal V)) :
    rho (clauseValue (ringAlgebra R) value ls) =
      clauseValue (ringAlgebra S) (fun v => rho (value v)) ls := by
  induction ls with
  | nil => simp [clauseValue, ringAlgebra]
  | cons l ls ih =>
      change rho (literalValue (ringAlgebra R) value l * clauseValue (ringAlgebra R) value ls) =
        literalValue (ringAlgebra S) (fun v => rho (value v)) l *
          clauseValue (ringAlgebra S) (fun v => rho (value v)) ls
      rw [map_mul, map_literalValue, ih]

theorem map_rowValue (rho : R →+* S) (decode : C → R) (value : V → R)
    (terms : SparseRow V C) :
    rho (rowValue (ringAlgebra R) decode value terms) =
      rowValue (ringAlgebra S) (fun c => rho (decode c)) (fun v => rho (value v)) terms := by
  induction terms with
  | nil => simp [rowValue, ringAlgebra]
  | cons term rest ih =>
      rcases term with ⟨c, ls⟩
      change rho (decode c * clauseValue (ringAlgebra R) value ls +
        rowValue (ringAlgebra R) decode value rest) =
        rho (decode c) * clauseValue (ringAlgebra S) (fun v => rho (value v)) ls +
          rowValue (ringAlgebra S) (fun c => rho (decode c)) (fun v => rho (value v)) rest
      rw [map_add, map_mul, map_clauseValue, ih]

end Naturality

namespace TernaryLift

variable {d : ℕ} (a : RingModel.Data d) (t : ℕ)

/-- The actual coefficient value used by the hash circuit. -/
noncomputable def coefficient (c : ZMod 3) : a.O t := (c.val : a.O t)

@[simp] theorem reduction_coefficient (ht : 0 < t) (c : ZMod 3) :
    a.rho t ht (coefficient a t c) = LiftRing.of a.residuePolynomial c := by
  rw [coefficient, map_natCast]
  conv_rhs => rw [← ZMod.natCast_zmod_val c]
  rw [map_natCast]

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

omit [DecidableEq E] in
/-- This is the origin equality needed by the selector: evaluate the integer
lift in the actual thickened ring, then reduce to the embedded ternary hash. -/
theorem reduction_hash (ht : 0 < t) (C : E → SAT.Clause V)
    (row : E → ZMod 3) (x : SAT.Assignment V) :
    a.rho t ht
      (MvPolynomial.eval (fun v => HashInput.boolValue (R := a.O t) (x v))
        (HashInput.hashPolynomial C (fun e => coefficient a t (row e)))) =
      LiftRing.of a.residuePolynomial
        (∑ e, row e * HashInput.violationVector (R := ZMod 3) C x e) := by
  rw [HashInput.eval_hashPolynomial, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [map_mul, map_mul, reduction_coefficient]
  congr 1
  cases h : (C e).eval x <;> simp [HashInput.violationVector, HashInput.clauseValue, h]

omit [DecidableEq V] in
/-- Sparse-list version of the same bridge, matching the executable evaluator's
input representation and preserving empty rows and empty clauses. -/
theorem reduction_sparseRow (ht : 0 < t) (x : SAT.Assignment V)
    (terms : SparseRow V (ZMod 3)) :
    a.rho t ht
      (rowValue (ringAlgebra (a.O t)) (coefficient a t)
        (fun v => HashInput.boolValue (R := a.O t) (x v)) terms) =
      LiftRing.of a.residuePolynomial
        (rowValue (ringAlgebra (ZMod 3)) id
          (fun v => HashInput.boolValue (R := ZMod 3) (x v)) terms) := by
  rw [map_rowValue, map_rowValue]
  congr 1
  · funext c
    exact reduction_coefficient a t ht c
  · funext v
    cases h : x v <;> simp [HashInput.boolValue ]

end TernaryLift
end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
