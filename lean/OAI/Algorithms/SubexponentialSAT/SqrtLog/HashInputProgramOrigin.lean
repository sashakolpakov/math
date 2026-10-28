import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramLift
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamily
import OAI.Algorithms.SubexponentialSAT.Encoding

namespace OAI.Algorithms

/-! Exact original-clause provenance for a raw tuple, including repetitions.
The integer lift is taken BEFORE the tuple terms are added; its reduction, not
its value in the thickened ring, equals the combined ternary selector row. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram
open scoped BigOperators
open LeafProgram

def rawRow {V : Type*} {m depth : ℕ}
    (source : Fin m → List (SAT.Literal V)) (h : HashFamily.Candidate m depth) :
    SparseRow V (ZMod 3) :=
  List.ofFn fun j => (h.2 j, source (h.1 j))

@[simp] theorem rawRow_length {V : Type*} {m depth : ℕ}
    (source : Fin m → List (SAT.Literal V)) (h : HashFamily.Candidate m depth) :
    (rawRow source h).length=depth := by simp [rawRow]

theorem rawRow_member {V : Type*} {m depth : ℕ}
    (source : Fin m → List (SAT.Literal V)) (h : HashFamily.Candidate m depth)
    (term : ZMod 3 × List (SAT.Literal V)) :
    term ∈ rawRow source h ↔ ∃ j, term=(h.2 j,source (h.1 j)) := by
  simp [rawRow,eq_comm]

theorem rawRow_width {V : Type*} {m depth k : ℕ}
    (source : Fin m → List (SAT.Literal V)) (h : HashFamily.Candidate m depth)
    (hw : ∀ i, (source i).length ≤ k) :
    ∀ term ∈ rawRow source h, term.2.length ≤ k := by
  intro term ht
  obtain ⟨j,rfl⟩ := (rawRow_member source h term).mp ht
  exact hw _

theorem rawRow_literal_count {V : Type*} {m depth k : ℕ}
    (source : Fin m → List (SAT.Literal V)) (h : HashFamily.Candidate m depth)
    (hw : ∀ i, (source i).length ≤ k) :
    ((rawRow source h).map fun term => term.2.length).sum ≤ depth*k := by
  simp only [rawRow,List.map_ofFn,List.sum_ofFn]
  calc
    (∑ j : Fin depth, (source (h.1 j)).length) ≤ ∑ _j : Fin depth, k :=
      Finset.sum_le_sum (fun j _ => hw _)
    _ = depth*k := by simp

theorem rowValue_eq_sum {V C R : Type*} [CommRing R]
    (decode : C → R) (value : V → R) (terms : SparseRow V C) :
    rowValue (ringAlgebra R) decode value terms =
      (terms.map fun term => decode term.1 * clauseValue (ringAlgebra R) value term.2).sum := by
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      rcases term with ⟨c,ls⟩
      change decode c * clauseValue (ringAlgebra R) value ls +
        rowValue (ringAlgebra R) decode value terms = _
      simp only [List.map_cons,List.sum_cons]
      rw [ih]

theorem rawRow_value {V R : Type*} [CommRing R] {m depth : ℕ}
    (source : Fin m → List (SAT.Literal V)) (h : HashFamily.Candidate m depth)
    (decode : ZMod 3 → R) (value : V → R) :
    rowValue (ringAlgebra R) decode value (rawRow source h) =
      ∑ j, decode (h.2 j) * clauseValue (ringAlgebra R) value (source (h.1 j)) := by
  simp [rowValue_eq_sum,rawRow,List.sum_ofFn]

theorem clauseValue_original {V R : Type*} [DecidableEq V] [CommRing R]
    (ls : List (SAT.Literal V)) (x : SAT.Assignment V) :
    clauseValue (ringAlgebra R) (fun v => HashInput.boolValue (R := R) (x v)) ls =
      HashInput.clauseValue ls.toFinset x := by
  induction ls with
  | nil => simp [clauseValue,ringAlgebra,HashInput.clauseValue]
  | cons l ls ih =>
      have hl : literalValue (ringAlgebra R)
          (fun v => HashInput.boolValue (R := R) (x v)) l =
          if l.eval x then (0:R) else 1 := by
        rcases l with ⟨v,p⟩
        cases p <;> cases hx : x v <;>
          simp [literalValue,ringAlgebra,HashInput.boolValue,SAT.Literal.eval,hx]
      change literalValue (ringAlgebra R) _ l * clauseValue (ringAlgebra R) _ ls = _
      rw [hl,ih]
      cases h1 : l.eval x <;> cases h2 : SAT.Clause.eval x ls.toFinset <;>
        simp [HashInput.clauseValue,SAT.Clause.eval_insert,h1,h2]

/-- This is the selector-origin theorem for the actual raw tuple expansion.
It handles repeated IDs and coefficients zero without a deduplication premise. -/
theorem rawRow_reduction {V : Type*} [DecidableEq V] {m depth d : ℕ}
    (a : RingModel.Data d) (t : ℕ) (ht : 0 < t)
    (source : Fin m → List (SAT.Literal V)) (h : HashFamily.Candidate m depth)
    (x : SAT.Assignment V) :
    a.rho t ht (rowValue (ringAlgebra (a.O t))
      (TernaryLift.coefficient a t)
      (fun v => HashInput.boolValue (R := a.O t) (x v)) (rawRow source h)) =
      SubexponentialSAT.LiftRing.of a.residuePolynomial
        (∑ i, HashFamily.row h i *
          HashInput.violationVector (R := ZMod 3) (fun e => (source e).toFinset) x i) := by
  rw [TernaryLift.reduction_sparseRow a t ht x,rawRow_value,HashFamily.row_dot]
  congr 1
  unfold HashFamily.eval
  apply Finset.sum_congr rfl
  intro j _
  rw [clauseValue_original]
  rfl

def clausePayload {n : ℕ} (ls : List (SAT.Literal (Fin n))) : List Bool :=
  Encoding.encodeList (fun l => Encoding.encodeNat (Encoding.literalCode l)) ls

def weightedPayload {n : ℕ} (weight : List Bool) (ls : List (SAT.Literal (Fin n))) : List Bool :=
  Encoding.frame weight ++ clausePayload ls

/-- Original literal byte order is retained, including repeated literals. -/
theorem clausePayload_codes {n : ℕ} (ls : List (SAT.Literal (Fin n))) :
    clausePayload ls = Encoding.encodeList Encoding.encodeNat (ls.map Encoding.literalCode) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
      change true :: (Encoding.frame (Encoding.encodeNat (Encoding.literalCode l)) ++
        clausePayload ls) = _
      simp only [List.map_cons,Encoding.encodeList]
      rw [ih]

end SubexponentialSAT.SqrtLog.HashInputProgram

end OAI.Algorithms
