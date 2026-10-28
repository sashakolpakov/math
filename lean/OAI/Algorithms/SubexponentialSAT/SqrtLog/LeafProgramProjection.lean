import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramHash

namespace OAI.Algorithms

/-! Sparse hash circuits commute with a canonical additive projection whose
product is stable. This is the bridge from truncated sparse operations to the
single untruncated source polynomial; no false ring-homomorphism claim about
canonical representatives is required. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram

variable {V C R : Type*} [CommRing R]

def projectedAlgebra (project : R →+ R) : Algebra R where
  zero := 0
  one := project 1
  add := (· + ·)
  mul := fun x y => project (x * y)
  neg := Neg.neg

theorem literalValue_projected (project : R →+ R) (value : V → R)
    (l : SAT.Literal V) :
    literalValue (projectedAlgebra project) (fun v => project (value v)) l =
      project (literalValue (ringAlgebra R) value l) := by
  cases hp : l.positive <;>
    simp [literalValue, projectedAlgebra, ringAlgebra, hp]

theorem clauseValue_projected (project : R →+ R)
    (hprod : ∀ x y, project (project x * project y) = project (x * y))
    (value : V → R) (ls : List (SAT.Literal V)) :
    clauseValue (projectedAlgebra project) (fun v => project (value v)) ls =
      project (clauseValue (ringAlgebra R) value ls) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
      change project (literalValue (projectedAlgebra project) (fun v => project (value v)) l *
        clauseValue (projectedAlgebra project) (fun v => project (value v)) ls) = _
      rw [literalValue_projected, ih, hprod]
      rfl

theorem rowValue_projected (project : R →+ R)
    (hprod : ∀ x y, project (project x * project y) = project (x * y))
    (decode : C → R) (value : V → R) (terms : SparseRow V C) :
    rowValue (projectedAlgebra project) (fun c => project (decode c))
      (fun v => project (value v)) terms =
      project (rowValue (ringAlgebra R) decode value terms) := by
  induction terms with
  | nil => exact (map_zero project).symm
  | cons term terms ih =>
      rcases term with ⟨c, ls⟩
      change project (project (decode c) *
          clauseValue (projectedAlgebra project) (fun v => project (value v)) ls) +
        rowValue (projectedAlgebra project) (fun c => project (decode c))
          (fun v => project (value v)) terms = _
      rw [clauseValue_projected project hprod, ih, hprod, ← map_add]
      rfl

theorem rowValue_projected_eq_eval (project : R →+ R)
    (hprod : ∀ x y, project (project x * project y) = project (x * y))
    (decode : C → R) (value : V → R) (terms : SparseRow V C) :
    rowValue (projectedAlgebra project) (fun c => project (decode c))
      (fun v => project (value v)) terms =
      project (MvPolynomial.eval value (rowPolynomial decode terms)) := by
  rw [rowValue_projected project hprod, rowValue_eq_eval]

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
