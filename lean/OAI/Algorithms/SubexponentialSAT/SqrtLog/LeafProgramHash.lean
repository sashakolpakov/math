import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInput
import OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost

namespace OAI.Algorithms

/-!
# Sparse clause-circuit evaluation for one hash row

The input is a list of supplied nonzero coefficients and width-k clause lists.
The evaluator visits those lists directly; it never builds a truth table on the
union of the clause scopes. Counters include measured variable lookup and ring
callbacks. Their primitive realization is a separate obligation, not inferred
from these counters. `Algebra` also admits canonical truncated operations, whose
decoder need not be a homomorphism into the untruncated polynomial ring.
-/

namespace SubexponentialSAT.SqrtLog.LeafProgram

open SubexponentialSAT.SubexpSymbolicCost

structure Algebra (A : Type*) where
  zero : A
  one : A
  add : A → A → A
  mul : A → A → A
  neg : A → A

structure Represents {C A : Type*} (ops : RingProgram C) (alg : Algebra A)
    (decode : C → A) : Prop where
  zero : decode ops.zeroRun.1 = alg.zero
  one : decode ops.oneRun.1 = alg.one
  add : ∀ a b, decode (ops.addRun a b).1 = alg.add (decode a) (decode b)
  mul : ∀ a b, decode (ops.mulRun a b).1 = alg.mul (decode a) (decode b)
  neg : ∀ a, decode (ops.negRun a).1 = alg.neg (decode a)

abbrev SparseRow (V C : Type*) := List (C × List (SAT.Literal V))

variable {V C A : Type*}

def literalValue (alg : Algebra A) (value : V → A) (l : SAT.Literal V) : A :=
  if l.positive then alg.add alg.one (alg.neg (value l.variable))
  else value l.variable

def clauseValue (alg : Algebra A) (value : V → A) : List (SAT.Literal V) → A
  | [] => alg.one
  | l :: ls => alg.mul (literalValue alg value l) (clauseValue alg value ls)

def rowValue (alg : Algebra A) (decode : C → A) (value : V → A) : SparseRow V C → A
  | [] => alg.zero
  | (c, ls) :: rest =>
      alg.add (alg.mul (decode c) (clauseValue alg value ls))
        (rowValue alg decode value rest)

def literalRun (ops : RingProgram C) (value : V → C × ℕ) (l : SAT.Literal V) : C × ℕ :=
  let v := value l.variable
  if l.positive then
    let neg := ops.negRun v.1
    let out := ops.addRun ops.oneRun.1 neg.1
    (out.1, v.2 + ops.oneRun.2 + neg.2 + out.2 + 1)
  else (v.1, v.2 + 1)

def clauseRun (ops : RingProgram C) (value : V → C × ℕ) : List (SAT.Literal V) → C × ℕ
  | [] => ops.oneRun
  | l :: ls =>
      let v := literalRun ops value l
      let rest := clauseRun ops value ls
      let out := ops.mulRun v.1 rest.1
      (out.1, v.2 + rest.2 + out.2 + 1)

def rowRun (ops : RingProgram C) (value : V → C × ℕ) : SparseRow V C → C × ℕ
  | [] => ops.zeroRun
  | (c, ls) :: terms =>
      let clause := clauseRun ops value ls
      let weighted := ops.mulRun c clause.1
      let rest := rowRun ops value terms
      let out := ops.addRun weighted.1 rest.1
      (out.1, clause.2 + weighted.2 + rest.2 + out.2 + 1)

theorem literalRun_correct (ops : RingProgram C) (alg : Algebra A) (decode : C → A)
    (h : Represents ops alg decode) (value : V → C × ℕ) (l : SAT.Literal V) :
    decode (literalRun ops value l).1 =
      literalValue alg (fun v => decode (value v).1) l := by
  cases hp : l.positive <;> simp [literalRun, literalValue, hp, h.add, h.one, h.neg]

theorem clauseRun_correct (ops : RingProgram C) (alg : Algebra A) (decode : C → A)
    (h : Represents ops alg decode) (value : V → C × ℕ) (ls : List (SAT.Literal V)) :
    decode (clauseRun ops value ls).1 =
      clauseValue alg (fun v => decode (value v).1) ls := by
  induction ls with
  | nil => exact h.one
  | cons l ls ih =>
      simp only [clauseRun, h.mul, literalRun_correct ops alg decode h, ih, clauseValue]

theorem rowRun_correct (ops : RingProgram C) (alg : Algebra A) (decode : C → A)
    (h : Represents ops alg decode) (value : V → C × ℕ) (terms : SparseRow V C) :
    decode (rowRun ops value terms).1 =
      rowValue alg decode (fun v => decode (value v).1) terms := by
  induction terms with
  | nil => exact h.zero
  | cons term rest ih =>
      rcases term with ⟨c, ls⟩
      simp only [rowRun, h.add, h.mul, clauseRun_correct ops alg decode h, ih, rowValue]

theorem literalRun_cost (ops : RingProgram C) {q b : ℕ}
    (hq : ProgramBudget ops q) (value : V → C × ℕ)
    (hv : ∀ v, (value v).2 ≤ b) (l : SAT.Literal V) :
    (literalRun ops value l).2 ≤ b + 3 * q + 1 := by
  have hval := hv l.variable
  have hn := hq.neg (value l.variable).1
  have ha := hq.add ops.oneRun.1 (ops.negRun (value l.variable).1).1
  have ho := hq.one
  cases hp : l.positive <;> simp only [literalRun, hp, Bool.false_eq_true,
    ↓reduceIte ] <;> omega

theorem clauseRun_cost (ops : RingProgram C) {q b : ℕ}
    (hq : ProgramBudget ops q) (value : V → C × ℕ)
    (hv : ∀ v, (value v).2 ≤ b) (ls : List (SAT.Literal V)) :
    (clauseRun ops value ls).2 ≤ q + ls.length * (b + 4 * q + 2) := by
  induction ls with
  | nil => simpa [clauseRun] using hq.one
  | cons l ls ih =>
      have hl := literalRun_cost ops hq value hv l
      have hm := hq.mul (literalRun ops value l).1 (clauseRun ops value ls).1
      simp only [clauseRun, List.length_cons ]
      nlinarith

theorem rowRun_cost (ops : RingProgram C) {q b k : ℕ}
    (hq : ProgramBudget ops q) (value : V → C × ℕ)
    (hv : ∀ v, (value v).2 ≤ b) (terms : SparseRow V C)
    (hk : ∀ term ∈ terms, term.2.length ≤ k) :
    (rowRun ops value terms).2 ≤
      q + terms.length * (3 * q + k * (b + 4 * q + 2) + 1) := by
  induction terms with
  | nil => simpa [rowRun] using hq.zero
  | cons term terms ih =>
      rcases term with ⟨c, ls⟩
      have hlen : ls.length ≤ k := hk (c, ls) (by simp)
      have hc := clauseRun_cost ops hq value hv ls
      have hm := hq.mul c (clauseRun ops value ls).1
      have ha := hq.add (ops.mulRun c (clauseRun ops value ls).1).1 (rowRun ops value terms).1
      have ht := ih (fun term hterm => hk term (List.mem_cons_of_mem _ hterm))
      have hsize := Nat.mul_le_mul_right (b + 4 * q + 2) hlen
      simp only [rowRun, List.length_cons ]
      nlinarith

def ringAlgebra (R : Type*) [CommRing R] : Algebra R :=
  ⟨0, 1, (· + ·), (· * ·), Neg.neg⟩

theorem representedRing_correct {R : Type*} [CommRing R] (ops : RepresentedRing C R) :
    Represents ops.program (ringAlgebra R) ops.decode :=
  ⟨ops.zero_correct, ops.one_correct, ops.add_correct, ops.mul_correct, ops.neg_correct⟩

section PolynomialSemantics

variable {R : Type*} [CommRing R]

noncomputable def clausePolynomial (ls : List (SAT.Literal V)) : MvPolynomial V R :=
  (ls.map HashInput.falsifyingLiteral).prod

noncomputable def rowPolynomial (decode : C → R) (terms : SparseRow V C) : MvPolynomial V R :=
  (terms.map fun term => MvPolynomial.C (decode term.1) * clausePolynomial term.2).sum

theorem clauseValue_eq_eval (value : V → R) (ls : List (SAT.Literal V)) :
    clauseValue (ringAlgebra R) value ls = MvPolynomial.eval value (clausePolynomial ls) := by
  induction ls with
  | nil => simp [clauseValue, clausePolynomial, ringAlgebra]
  | cons l ls ih =>
      change literalValue (ringAlgebra R) value l * clauseValue (ringAlgebra R) value ls = _
      simp only [clausePolynomial, List.map_cons, List.prod_cons, map_mul]
      rw [ih]
      congr 1
      cases hp : l.positive <;>
        simp [literalValue, ringAlgebra, HashInput.falsifyingLiteral, hp, sub_eq_add_neg]

theorem rowValue_eq_eval (decode : C → R) (value : V → R) (terms : SparseRow V C) :
    rowValue (ringAlgebra R) decode value terms =
      MvPolynomial.eval value (rowPolynomial decode terms) := by
  induction terms with
  | nil => simp [rowValue, rowPolynomial, ringAlgebra]
  | cons term terms ih =>
      rcases term with ⟨c, ls⟩
      change decode c * clauseValue (ringAlgebra R) value ls +
        rowValue (ringAlgebra R) decode value terms = _
      rw [clauseValue_eq_eval, ih]
      simp [rowPolynomial]

theorem rowRun_eq_eval (ops : RepresentedRing C R) (value : V → C × ℕ)
    (terms : SparseRow V C) :
    ops.decode (rowRun ops.program value terms).1 =
      MvPolynomial.eval (fun v => ops.decode (value v).1) (rowPolynomial ops.decode terms) := by
  rw [rowRun_correct ops.program (ringAlgebra R) ops.decode (representedRing_correct ops)]
  exact rowValue_eq_eval _ _ _

end PolynomialSemantics
end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
