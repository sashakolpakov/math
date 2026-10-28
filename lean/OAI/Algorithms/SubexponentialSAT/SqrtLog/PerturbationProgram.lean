import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDensePolynomial
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsPerturbation
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsStored

namespace OAI.Algorithms

/-! Explicit coefficient preparation for incidence perturbations.
The coefficient arrays are ordered from degree zero upwards. Every shift and
node evaluation is the existing finite represented-ring loop, not an oracle.
Counters here charge coefficient callbacks and list visits; primitive execution
is a separate interface and is not asserted by these counter theorems. -/
namespace SubexponentialSAT.SqrtLog.PerturbationProgram

open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpDensePolynomial
open scoped BigOperators

variable {C R : Type*} [CommRing R]

noncomputable def polynomial (ops : RepresentedRing C R) (p : List C) : Polynomial R :=
  PolynomialAlgorithm.denote (decodeList ops p)

/-- An explicit Horner evaluation and an explicit translated coefficient array. -/
def coordinateRun (ops : RepresentedRing C R) (theta : C) (p : List C) :
    (C × List C) × ℕ :=
  let node := evalRun ops theta p
  let shifted := shiftRun ops theta p
  ((node.1, shifted.1), node.2 + shifted.2 + p.length)

@[simp] theorem coordinateRun_node (ops : RepresentedRing C R) (theta : C) (p : List C) :
    ops.decode (coordinateRun ops theta p).1.1 = (polynomial ops p).eval (ops.decode theta) := by
  simp only [coordinateRun, evalRun_correct, PolynomialAlgorithm.eval_eq, polynomial]

@[simp] theorem coordinateRun_shift (ops : RepresentedRing C R) (theta : C) (p : List C) :
    polynomial ops (coordinateRun ops theta p).1.2 =
      (polynomial ops p).comp (Polynomial.X + Polynomial.C (ops.decode theta)) := by
  simp only [coordinateRun, polynomial, shiftRun_correct, PolynomialAlgorithm.denote_shift]

theorem coordinateRun_length (ops : RepresentedRing C R) (theta : C) (p : List C) :
    (coordinateRun ops theta p).1.2.length ≤ 2 * p.length :=
  shiftRun_length ops theta p

theorem coordinateRun_cost (ops : RepresentedRing C R) {q : ℕ}
    (budget : ScalarBudget ops q) (theta : C) (p : List C) :
    (coordinateRun ops theta p).2 ≤ (4*p.length^2 + 2*p.length + 1)*q + p.length := by
  have he := evalRun_cost ops budget theta p
  have hs := shiftRun_cost ops budget theta p
  dsimp only [coordinateRun]
  nlinarith

/-- Removing the constant coefficient creates the actual positive-Z row delta. -/
def positiveRun (ops : RepresentedRing C R) (theta : C) (p : List C) : List C :=
  ops.zeroRun.1 :: (coordinateRun ops theta p).1.2.tail

private theorem denote_zero_tail (p : List R) :
    PolynomialAlgorithm.denote (0 :: p.tail) =
      PolynomialAlgorithm.denote p - Polynomial.C ((PolynomialAlgorithm.denote p).eval 0) := by
  cases p with
  | nil => simp
  | cons a p => simp

/-- This is the same polynomial as Moments.rowDelta, with no constant term. -/
theorem positiveRun_correct (ops : RepresentedRing C R) (theta : C) (p : List C) :
    polynomial ops (positiveRun ops theta p) =
      Moments.rowDelta (polynomial ops p) (ops.decode theta) := by
  have htail (l : List C) : decodeList ops l.tail = (decodeList ops l).tail := by
    cases l <;> rfl
  unfold positiveRun polynomial
  rw [show decodeList ops (ops.zeroRun.1 :: (coordinateRun ops theta p).1.2.tail) =
    0 :: (decodeList ops (coordinateRun ops theta p).1.2).tail by
      simp only [SubexpDensePolynomial.decodeList, List.map_cons, ops.zero_correct, List.map_tail]]
  rw [denote_zero_tail]
  change polynomial ops (coordinateRun ops theta p).1.2 -
      Polynomial.C ((polynomial ops (coordinateRun ops theta p).1.2).eval 0) = _
  rw [coordinateRun_shift]
  simp [Moments.rowDelta, polynomial]

/-- The local head chooses the current assignment; other heads use the fixed
bucket representative. This selection is executable Boolean data. -/
def selected {V G : Type*} [DecidableEq G] (head : V → G) (g : G)
    (current representative : V → Bool) (v : V) : Bool :=
  if head v = g then current v else representative v

/-- A dot product against a Boolean vector: rejected entries perform no
multiplication, and selected entries use the explicit ring addition callback. -/
def betaRun (ops : RepresentedRing C R) (theta : C) : List (List C × Bool) → C × ℕ
  | [] => ops.zeroRun
  | (p, use) :: rows =>
      let rest := betaRun ops theta rows
      if use then
        let node := evalRun ops theta p
        let out := ops.addRun node.1 rest.1
        (out.1, rest.2 + node.2 + out.2 + 1)
      else (rest.1, rest.2 + 1)

noncomputable def betaValue (ops : RepresentedRing C R) (theta : C)
    (rows : List (List C × Bool)) : R :=
  (rows.map fun a => if a.2 then (polynomial ops a.1).eval (ops.decode theta) else 0).sum

theorem betaRun_correct (ops : RepresentedRing C R) (theta : C)
    (rows : List (List C × Bool)) :
    ops.decode (betaRun ops theta rows).1 = betaValue ops theta rows := by
  induction rows with
  | nil => exact ops.zero_correct
  | cons a rows ih =>
      rcases a with ⟨p,b⟩
      cases b <;> simp [betaRun, betaValue, ops.add_correct, evalRun_correct,
        PolynomialAlgorithm.eval_eq, polynomial, ih, betaValue] at *

theorem betaRun_cost (ops : RepresentedRing C R) {q : ℕ}
    (budget : ScalarBudget ops q) (theta : C) (rows : List (List C × Bool))
    (L : ℕ) (hL : ∀ a ∈ rows, a.1.length ≤ L) :
    (betaRun ops theta rows).2 ≤ q + rows.length * ((2*L+2)*q+1) := by
  induction rows with
  | nil => simpa [betaRun] using budget.zero
  | cons a rows ih =>
      rcases a with ⟨p,b⟩
      have hp := hL (p,b) (by simp)
      have hr := ih (by intro a ha; exact hL a (by simp [ha]))
      have he := evalRun_cost ops budget theta p
      have ha := budget.add (evalRun ops theta p).1 (betaRun ops theta rows).1
      cases b <;> simp only [betaRun, Bool.false_eq_true, ↓reduceIte, List.length_cons] <;>
        nlinarith

/-- One physical output key. Only the origin and positive-Z singleton keys
are emitted by the incidence preparer. -/
def singletonKey {V : Type*} [DecidableEq V] (v : V) (j : ℕ) : Squarefree.Index V :=
  ⟨0,j+1,{v}⟩

@[simp] theorem singletonKey_valid {V : Type*} [DecidableEq V] (v : V) (j : ℕ) :
    (singletonKey v j).Valid := by simp [singletonKey, Squarefree.Index.Valid]

/-- Explicit row emission loop. The input is the tail of the translated array;
position j stores the coefficient of Z^(j+1), never the node value. -/
def emitPositive {V : Type*} [DecidableEq V] (v : V) (J : ℕ) (j : ℕ) :
    List C → List (Squarefree.Index V × C)
  | [] => []
  | c :: cs =>
      if j+1 < J then (singletonKey v j,c) :: emitPositive v J (j+1) cs else []

theorem emitPositive_length {V : Type*} [DecidableEq V] (v : V) (J j : ℕ) (p : List C) :
    (emitPositive v J j p).length ≤ p.length := by
  induction p generalizing j with
  | nil => simp [emitPositive]
  | cons c cs ih =>
      simp only [emitPositive]
      split <;> simp only [List.length_cons, List.length_nil]
      · exact Nat.add_le_add_right (ih (j+1)) 1
      · omega

theorem emitPositive_mem {V : Type*} [DecidableEq V] (v : V) (J j : ℕ)
    (p : List C) (a : Squarefree.Index V × C) (ha : a ∈ emitPositive v J j p) :
    a.1.u = 0 ∧ a.1.z < J ∧ 0 < a.1.z ∧ a.1.vars = {v} := by
  induction p generalizing j with
  | nil => simp [emitPositive] at ha
  | cons c cs ih =>
      simp only [emitPositive] at ha
      split at ha
      next h =>
        rcases List.mem_cons.mp ha with h | h
        · subst a; exact ⟨rfl,‹j+1 < J›,by simp [singletonKey],rfl⟩
        · exact ih (j+1) h
      next => simp at ha

end SubexponentialSAT.SqrtLog.PerturbationProgram

end OAI.Algorithms
