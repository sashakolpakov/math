import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramStored

namespace OAI.Algorithms

/-! Left-fold semantics for the physical record interpreter. Canonical sparse
lists need not be equal under reassociation; their denotations are the same
canonical projection of the common source polynomial. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram

variable {V C R : Type*} [CommRing R]

def clauseFoldValue (alg : Algebra R) (value : V → R)
    (ls : List (SAT.Literal V)) (init : R) : R :=
  ls.foldl (fun acc l => alg.mul acc (literalValue alg value l)) init

def rowFoldValue (alg : Algebra R) (decode : C → R) (value : V → R)
    (terms : SparseRow V C) (init : R) : R :=
  terms.foldl (fun acc term =>
    alg.add acc (alg.mul (decode term.1) (clauseValue alg value term.2))) init

theorem clauseFoldValue_projected (project : R →+ R)
    (hprod : ∀ x y, project (project x * project y) = project (x * y))
    (value : V → R) (ls : List (SAT.Literal V)) (init : R) :
    clauseFoldValue (projectedAlgebra project) (fun v => project (value v)) ls (project init) =
      project (init * clauseValue (ringAlgebra R) value ls) := by
  induction ls generalizing init with
  | nil => simp [clauseFoldValue, clauseValue, ringAlgebra]
  | cons l ls ih =>
      change clauseFoldValue (projectedAlgebra project) (fun v => project (value v)) ls
        (project (project init * literalValue (projectedAlgebra project)
          (fun v => project (value v)) l)) = _
      rw [literalValue_projected, hprod, ih]
      change project ((init * literalValue (ringAlgebra R) value l) *
        clauseValue (ringAlgebra R) value ls) =
          project (init * (literalValue (ringAlgebra R) value l * clauseValue (ringAlgebra R) value ls))
      rw [mul_assoc]

theorem clauseFoldValue_projected_one (project : R →+ R)
    (hprod : ∀ x y, project (project x * project y) = project (x * y))
    (value : V → R) (ls : List (SAT.Literal V)) :
    clauseFoldValue (projectedAlgebra project) (fun v => project (value v)) ls (project 1) =
      clauseValue (projectedAlgebra project) (fun v => project (value v)) ls := by
  rw [clauseFoldValue_projected project hprod, one_mul, clauseValue_projected project hprod]

theorem rowFoldValue_projected (project : R →+ R)
    (hprod : ∀ x y, project (project x * project y) = project (x * y))
    (decode : C → R) (value : V → R) (terms : SparseRow V C) (init : R) :
    rowFoldValue (projectedAlgebra project) (fun c => project (decode c))
      (fun v => project (value v)) terms (project init) =
      project (init + rowValue (ringAlgebra R) decode value terms) := by
  induction terms generalizing init with
  | nil => simp [rowFoldValue, rowValue, ringAlgebra]
  | cons term terms ih =>
      rcases term with ⟨c, ls⟩
      change rowFoldValue (projectedAlgebra project) (fun c => project (decode c))
        (fun v => project (value v)) terms
        (project init + project (project (decode c) *
          clauseValue (projectedAlgebra project) (fun v => project (value v)) ls)) = _
      rw [clauseValue_projected project hprod, hprod, ← map_add, ih]
      change project ((init + decode c * clauseValue (ringAlgebra R) value ls) +
        rowValue (ringAlgebra R) decode value terms) =
          project (init + (decode c * clauseValue (ringAlgebra R) value ls +
            rowValue (ringAlgebra R) decode value terms))
      rw [add_assoc]

theorem rowFoldValue_projected_zero (project : R →+ R)
    (hprod : ∀ x y, project (project x * project y) = project (x * y))
    (decode : C → R) (value : V → R) (terms : SparseRow V C) :
    rowFoldValue (projectedAlgebra project) (fun c => project (decode c))
      (fun v => project (value v)) terms 0 =
      rowValue (projectedAlgebra project) (fun c => project (decode c))
        (fun v => project (value v)) terms := by
  have h := rowFoldValue_projected project hprod decode value terms 0
  simpa only [map_zero, zero_add, rowValue_projected project hprod] using h

section Stored
variable [DecidableEq V] {vars : Finset V} {t J : ℕ}

theorem stored_clauseFoldValue
    (value : V → Moments.Stored (R := R) vars t J) (ls : List (SAT.Literal V)) :
    clauseFoldValue (squarefreeAlgebra t J) (fun v => (value v).denote) ls
      (Squarefree.canonical t J 1) =
        clauseValue (squarefreeAlgebra t J) (fun v => (value v).denote) ls := by
  have h := clauseFoldValue_projected_one (Squarefree.canonical t J)
    (Squarefree.canonical_mul t J) (fun v => (value v).denote) ls
  simpa only [Moments.Stored.canonical] using h

theorem stored_rowFoldValue
    (value : V → Moments.Stored (R := R) vars t J)
    (terms : SparseRow V (Moments.Stored (R := R) vars t J)) :
    rowFoldValue (squarefreeAlgebra t J) Moments.Stored.denote
      (fun v => (value v).denote) terms 0 =
        rowValue (squarefreeAlgebra t J) Moments.Stored.denote
          (fun v => (value v).denote) terms := by
  have h := rowFoldValue_projected_zero (Squarefree.canonical t J)
    (Squarefree.canonical_mul t J)
    (fun c : Moments.Stored (R := R) vars t J => c.denote) (fun v => (value v).denote) terms
  simpa only [Moments.Stored.canonical] using h

end Stored
end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
