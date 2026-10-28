import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpAlgorithm
import OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost

namespace OAI.Algorithms

/-!
# Measured evaluation with represented coefficients

The evaluator takes executable operations, each returning a value and its own
counter. It invokes each child and each operation once. Literal loading is an
operation too. No algebraic laws are imposed on stored coefficient words.

The generic counter theorem is a theorem about these actual recursive calls.
Turning the counter into primitive-machine time additionally requires the
local machine realizations of the supplied operations.
-/

namespace SubexponentialSAT.SubexpExecution

abbrev Expr := Algorithm.Expr

structure Operations (L C : Type*) where
  load : L → C × ℕ
  add : C → C → C × ℕ
  mul : C → C → C × ℕ

def evalWithCost {L C : Type*} (ops : Operations L C) : Expr L → C × ℕ
  | .lit x => ops.load x
  | .add e f =>
      let left := evalWithCost ops e
      let right := evalWithCost ops f
      let out := ops.add left.1 right.1
      (out.1, left.2 + right.2 + out.2)
  | .mul e f =>
      let left := evalWithCost ops e
      let right := evalWithCost ops f
      let out := ops.mul left.1 right.1
      (out.1, left.2 + right.2 + out.2)

/-- A structural predicate on literals; it is used only in proofs. -/
def EveryLiteral {L : Type*} (P : L → Prop) : Expr L → Prop
  | .lit x => P x
  | .add e f => EveryLiteral P e ∧ EveryLiteral P f
  | .mul e f => EveryLiteral P e ∧ EveryLiteral P f

theorem evalWithCost_valid {L C : Type*} (ops : Operations L C) (P : C → Prop)
    (hl : ∀ x, P (ops.load x).1)
    (ha : ∀ x y, P x → P y → P (ops.add x y).1)
    (hm : ∀ x y, P x → P y → P (ops.mul x y).1) (e : Expr L) :
    P (evalWithCost ops e).1 := by
  induction e with
  | lit x => exact hl x
  | add e f he hf => exact ha _ _ he hf
  | mul e f he hf => exact hm _ _ he hf

theorem evalWithCost_cost_le {L C : Type*} (ops : Operations L C) (P : C → Prop)
    (hl : ∀ x, P (ops.load x).1)
    (ha : ∀ x y, P x → P y → P (ops.add x y).1)
    (hm : ∀ x y, P x → P y → P (ops.mul x y).1)
    (B : ℕ)
    (hadd : ∀ x y, P x → P y → (ops.add x y).2 ≤ B)
    (hmul : ∀ x y, P x → P y → (ops.mul x y).2 ≤ B)
    (e : Expr L) (hload : EveryLiteral (fun x => (ops.load x).2 ≤ B) e) :
    (evalWithCost ops e).2 ≤ B * e.size := by
  induction e with
  | lit x => simpa [EveryLiteral, evalWithCost, Algorithm.Expr.size] using hload
  | add e f he hf =>
      have ce := he hload.1
      have cf := hf hload.2
      have co := hadd _ _ (evalWithCost_valid ops P hl ha hm e)
        (evalWithCost_valid ops P hl ha hm f)
      change (evalWithCost ops e).2 + (evalWithCost ops f).2 +
        (ops.add (evalWithCost ops e).1 (evalWithCost ops f).1).2 ≤ _
      simp only [Algorithm.Expr.size, Nat.mul_add, Nat.mul_one]
      omega
  | mul e f he hf =>
      have ce := he hload.1
      have cf := hf hload.2
      have co := hmul _ _ (evalWithCost_valid ops P hl ha hm e)
        (evalWithCost_valid ops P hl ha hm f)
      change (evalWithCost ops e).2 + (evalWithCost ops f).2 +
        (ops.mul (evalWithCost ops e).1 (evalWithCost ops f).1).2 ≤ _
      simp only [Algorithm.Expr.size, Nat.mul_add, Nat.mul_one]
      omega

theorem evalWithCost_decode {L C S : Type*} [Add S] [Mul S]
    (ops : Operations L C) (decode : C → S) (literal : L → S)
    (hl : ∀ x, decode (ops.load x).1 = literal x)
    (ha : ∀ x y, decode (ops.add x y).1 = decode x + decode y)
    (hm : ∀ x y, decode (ops.mul x y).1 = decode x * decode y)
    (e : Expr L) :
    decode (evalWithCost ops e).1 = (e.map literal).eval := by
  induction e with
  | lit x => exact hl x
  | add e f he hf =>
      change decode (ops.add _ _).1 = _
      rw [ha, he, hf]
      rfl
  | mul e f he hf =>
      change decode (ops.mul _ _).1 = _
      rw [hm, he, hf]
      rfl

/-- The measured evaluator's values agree with the existing postfix machine
using the very same callback values. -/
theorem evalWithCost_postfix {L C : Type*} (ops : Operations L C) (e : Expr L) :
    letI : Add C := ⟨fun x y => (ops.add x y).1⟩
    letI : Mul C := ⟨fun x y => (ops.mul x y).1⟩
    Computation.Trace Algorithm.step e.size
      ⟨(e.map fun x => (ops.load x).1).compile, []⟩
      ⟨[], [(evalWithCost ops e).1]⟩ := by
  let _ : Add C := ⟨fun x y => (ops.add x y).1⟩
  let _ : Mul C := ⟨fun x y => (ops.mul x y).1⟩
  have h := evalWithCost_decode ops id (fun x => (ops.load x).1)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) e
  simpa only [Algorithm.Expr.size_map, ← h, id_eq, List.append_nil] using
    (e.map fun x => (ops.load x).1).compile_trace [] []

theorem EveryLiteral.imp {L : Type*} {P Q : L → Prop} (h : ∀ x, P x → Q x)
    (e : Expr L) (he : EveryLiteral P e) : EveryLiteral Q e := by
  induction e with
  | lit x => exact h x he
  | add e f he' hf' => exact ⟨he' he.1, hf' he.2⟩
  | mul e f he' hf' => exact ⟨he' he.1, hf' he.2⟩

private theorem map_map {L C S : Type*} (f : L → C) (g : C → S) (e : Expr L) :
    (e.map f).map g = e.map (fun x => g (f x)) := by
  induction e with
  | lit x => rfl
  | add e f he hf => simp [Algorithm.Expr.map, he, hf]
  | mul e f he hf => simp [Algorithm.Expr.map, he, hf]

open SymbolicCost SubexpSymbolicCost

/-- The runtime package contains only executable callbacks. In particular it
does not contain a quotient decoder or a proof of ring laws on code words. -/
def programOperations {D : ℕ} {C : Type*} (ops : RingProgram C)
    (slots : List (RawIndex D)) : Operations (CoeffList D C) (CoeffList D C) where
  load := programProject ops slots
  add := programAdd ops slots
  mul := programMul ops slots

def programEval {D : ℕ} {C : Type*} (ops : RingProgram C)
    (slots : List (RawIndex D)) (e : Expr (CoeffList D C)) : CoeffList D C × ℕ :=
  evalWithCost (programOperations ops slots) e

theorem project_length {D : ℕ} {C : Type*} (ops : RingProgram C)
    (slots : List (RawIndex D)) (P : CoeffList D C) :
    (programProject ops slots P).1.length = slots.length := by
  induction slots with
  | nil => rfl
  | cons a slots ih => simpa [programProject] using congrArg Nat.succ ih

theorem programEval_length {D : ℕ} {C : Type*} (ops : RingProgram C)
    (slots : List (RawIndex D)) (e : Expr (CoeffList D C)) :
    (programEval ops slots e).1.length = slots.length := by
  apply evalWithCost_valid (programOperations ops slots) (fun P => P.length = slots.length)
  · exact project_length ops slots
  · intro P Q _ _
    exact project_length ops slots _
  · intro P Q _ _
    exact project_length ops slots _

section Representation

variable {D : ℕ} {C R : Type*} [CommRing R] (ops : RepresentedRing C R)

/-- Decoder correctness follows every actual load/add/multiply in the loop.
The target uses the already verified dense coefficient-list operations. -/
theorem programEval_decode (slots : List (RawIndex D)) (e : Expr (CoeffList D C)) :
    decodeList ops (programEval ops.program slots e).1 =
      ((e.map fun raw => Algorithm.Dense.ofRaw slots (decodeList ops raw)).eval).coefficients := by
  induction e with
  | lit raw =>
      change decodeList ops (programProject ops.program slots raw).1 = _
      rw [programProject_represented, representedProject_correct]
      rfl
  | add e f he hf =>
      change decodeList ops (programAdd ops.program slots
        (programEval ops.program slots e).1 (programEval ops.program slots f).1).1 = _
      rw [programAdd_represented, representedAdd_correct, he, hf]
      rfl
  | mul e f he hf =>
      change decodeList ops (programMul ops.program slots
        (programEval ops.program slots e).1 (programEval ops.program slots f).1).1 = _
      rw [programMul_represented, representedMul_correct, he, hf]
      rfl

theorem programEval_denote (slots : List (RawIndex D)) (hn : slots.Nodup)
    (hs : ∀ a, a ∈ slots ↔ Retained D a) (e : Expr (CoeffList D C)) :
    denote (decodeList ops (programEval ops.program slots e).1) =
      Truncation.canonical (D + 1) D (2 * D + 1)
        ((e.map fun raw => denote (decodeList ops raw)).eval) := by
  rw [programEval_decode]
  have h := Algorithm.eval_dense_denote slots hn hs (e.map (decodeList ops))
  simpa only [map_map] using h

/-- Literal projection and both dense operations are included. The bound is
uniform in the scalar budget and maximum raw literal length. -/
def instructionBudget (N maxRaw scalarCost : ℕ) : ℕ :=
  N * ((scalarCost + 2) * maxRaw + scalarCost + 2) +
    (scalarCost + 3) * (denseAddCost N + denseCost N)

theorem programEval_cost {q : ℕ} (budget : ScalarBudget ops q)
    (slots : List (RawIndex D)) (maxRaw : ℕ) (e : Expr (CoeffList D C))
    (hraw : EveryLiteral (fun raw => raw.length ≤ maxRaw) e) :
    (programEval ops.program slots e).2 ≤
      instructionBudget slots.length maxRaw q * e.size := by
  apply evalWithCost_cost_le (programOperations ops.program slots)
    (fun P => P.length = slots.length)
    (project_length ops.program slots)
    (fun P Q _ _ => project_length ops.program slots _)
    (fun P Q _ _ => project_length ops.program slots _)
  · intro P Q hP hQ
    change (programAdd ops.program slots P Q).2 ≤ _
    rw [programAdd_represented]
    have h := representedAdd_cost ops budget slots P Q hP hQ
    unfold instructionBudget
    simp only [Nat.mul_add]
    omega
  · intro P Q hP hQ
    change (programMul ops.program slots P Q).2 ≤ _
    rw [programMul_represented]
    have h := representedMul_cost ops budget slots P Q hP hQ
    unfold instructionBudget
    simp only [Nat.mul_add]
    omega
  · apply EveryLiteral.imp (fun raw hlen => ?_) e hraw
    change (programProject ops.program slots raw).2 ≤ _
    rw [programProject_represented]
    have h := representedProject_cost ops budget slots raw
    have h' : slots.length * ((q + 2) * raw.length + q + 2) ≤
        slots.length * ((q + 2) * maxRaw + q + 2) := by gcongr
    exact (h.trans h').trans (Nat.le_add_right _ _)

end Representation

end SubexponentialSAT.SubexpExecution

end OAI.Algorithms
