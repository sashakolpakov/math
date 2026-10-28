import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputRestriction
import OAI.Algorithms.SubexponentialSAT.Subexp.PaddedCompletion

namespace OAI.Algorithms

/-! Physical merge of high and free Boolean assignments in original order.
This routine never renames a variable or drops an unused coordinate. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 4 4
abbrev Code := Cmd 4 4

def state (regs : Fin 4 → Bool) (mask high low out : List Bool) : Data :=
  ⟨regs, ![mask, high, low, out]⟩

def selected (choice : Bool) : List Bool → List Bool → List Bool
  | b :: bs, x :: xs => if b = choice then x :: selected choice bs xs else selected choice bs xs
  | _, _ => []

def popMask : Code := .base (.atom (.pop 0 0 1))
def loadBit : Code := .ite 0 (.base (.atom (.pop 1 2 3))) (.base (.atom (.pop 2 2 3)))
def pushBit : Code := .base (.atom (.push 3 2))
def body : Code := .seq loadBit (.seq pushBit popMask)
def loop : Code := .while 1 body
def command : Code := .seq popMask loop

def popped (regs : Fin 4 → Bool) (mask high low out : List Bool) : Data :=
  state (readRegs regs 0 1 mask.head?) mask.tail high low out

theorem popMask_eval (regs : Fin 4 → Bool) (mask high low out : List Bool) :
    Eval popMask 1 (state regs mask high low out) (popped regs mask high low out) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.pop (0 : Fin 4) 0 1)
    (state regs mask high low out))) using 1
  · rfl
  · apply congrArg (StructuredProgram.State.mk _)
    funext i
    fin_cases i <;> rfl

theorem iteration (regs : Fin 4 → Bool) (b x : Bool) (mask xs out : List Bool) :
    ∃ rf, Eval body 4
      (popped regs (b :: mask) (selected true (b :: mask) (x :: xs))
        (selected false (b :: mask) (x :: xs)) out)
      (popped rf mask (selected true mask xs) (selected false mask xs) (x :: out)) := by
  let a := popped regs (b :: mask) (selected true (b :: mask) (x :: xs))
    (selected false (b :: mask) (x :: xs)) out
  let r := readRegs (readRegs regs 0 1 (some b)) 2 3 (some x)
  refine ⟨r, ?_⟩
  have hp : Eval pushBit 1 (state r mask (selected true mask xs) (selected false mask xs) out)
      (state r mask (selected true mask xs) (selected false mask xs) (x :: out)) := by
    convert (Eval.base (StructuredProgram.Eval.atom (.push (3 : Fin 4) 2)
      (state r mask (selected true mask xs) (selected false mask xs) out))) using 1
    · rfl
    · apply congrArg (StructuredProgram.State.mk _)
      funext i
      fin_cases i <;> simp [r, state, readRegs,
        StructuredProgram.Atom.instr, execInstr]
  have hl : Eval loadBit 2 a
      (state r mask (selected true mask xs) (selected false mask xs) out) := by
    cases b with
    | false =>
        apply Eval.ite_false (by rfl)
        convert (Eval.base (StructuredProgram.Eval.atom (.pop (2 : Fin 4) 2 3) a)) using 1
        · apply congrArg (StructuredProgram.State.mk _)
          funext i
          fin_cases i <;> simp [a, popped, selected, state,
            StructuredProgram.Atom.instr, execInstr, readRegs]
    | true =>
        apply Eval.ite_true (by rfl)
        convert (Eval.base (StructuredProgram.Eval.atom (.pop (1 : Fin 4) 2 3) a)) using 1
        · apply congrArg (StructuredProgram.State.mk _)
          funext i
          fin_cases i <;> simp [a, popped, selected, state,
            StructuredProgram.Atom.instr, execInstr, readRegs]
  exact hl.seq (hp.seq (popMask_eval r mask (selected true mask xs) (selected false mask xs) (x :: out)))

theorem loop_eval (regs : Fin 4 → Bool) (mask xs out : List Bool)
    (hlen : mask.length = xs.length) :
    ∃ rf, Eval loop (5 * mask.length + 1)
      (popped regs mask (selected true mask xs) (selected false mask xs) out)
      (state rf [] [] [] (xs.reverse ++ out)) := by
  induction mask generalizing regs xs out with
  | nil =>
      have hx : xs = [] := List.eq_nil_of_length_eq_zero hlen.symm
      subst xs
      refine ⟨readRegs regs 0 1 none, ?_⟩
      exact Eval.while_false (by rfl)
  | cons b mask ih =>
      cases xs with
      | nil => simp at hlen
      | cons x xs =>
          obtain ⟨ri, hi⟩ := iteration regs b x mask xs out
          obtain ⟨rf, hr⟩ := ih ri xs (x :: out) (by simpa using hlen)
          refine ⟨rf, ?_⟩
          have h := Eval.while_true (show
            (popped regs (b :: mask) (selected true (b :: mask) (x :: xs))
              (selected false (b :: mask) (x :: xs)) out).regs 1 = true by rfl) hi hr
          convert h using 1 <;> simp only [loop, List.length_cons, List.reverse_cons, List.append_assoc,
            List.singleton_append, Nat.mul_add, Nat.mul_one,
            Nat.add_comm, Nat.add_left_comm] ; omega

theorem command_eval (regs : Fin 4 → Bool) (mask xs out : List Bool)
    (hlen : mask.length = xs.length) :
    ∃ rf, Eval command (5 * mask.length + 2)
      (state regs mask (selected true mask xs) (selected false mask xs) out)
      (state rf [] [] [] (xs.reverse ++ out)) := by
  obtain ⟨rf, hr⟩ := loop_eval regs mask xs out hlen
  refine ⟨rf, ?_⟩
  convert (popMask_eval regs mask (selected true mask xs) (selected false mask xs) out).seq hr using 1
  · rfl
  · omega

def program := compiled command 0 3

theorem program_runsIn (regs : Fin 4 → Bool) (mask xs out : List Bool)
    (hlen : mask.length = xs.length) :
    ∃ rf, RunsIn program (5 * mask.length + 3)
      ((state regs mask (selected true mask xs) (selected false mask xs) out).withPC
        (some program.entry))
      ((state rf [] [] [] (xs.reverse ++ out)).withPC none) := by
  obtain ⟨rf, hr⟩ := command_eval regs mask xs out hlen
  exact ⟨rf, 5 * mask.length + 2 + 1, by omega, compiled_halt_trace hr 0 3⟩


theorem selected_true_length (mask xs : List Bool) (hlen : mask.length = xs.length) :
    (selected true mask xs).length = Subexp.PaddedCompletion.trueCount mask := by
  induction mask generalizing xs with
  | nil => simp [selected, Subexp.PaddedCompletion.trueCount, Subexp.PaddedCompletion.successful]
  | cons b mask ih =>
      cases xs with
      | nil => simp at hlen
      | cons x xs =>
          have ht : mask.length = xs.length := by simpa using hlen
          cases b <;> simp [selected, Subexp.PaddedCompletion.trueCount,
            Subexp.PaddedCompletion.successful] at * <;> exact ih xs ht

theorem selected_pair_injective (mask xs ys : List Bool)
    (hx : mask.length = xs.length) (hy : mask.length = ys.length)
    (hh : selected true mask xs = selected true mask ys)
    (hl : selected false mask xs = selected false mask ys) : xs = ys := by
  induction mask generalizing xs ys with
  | nil =>
      have hxs : xs = [] := List.eq_nil_of_length_eq_zero hx.symm
      have hys : ys = [] := List.eq_nil_of_length_eq_zero hy.symm
      simp [hxs, hys]
  | cons b mask ih =>
      cases xs with
      | nil => simp at hx
      | cons x xs =>
          cases ys with
          | nil => simp at hy
          | cons y ys =>
              have hxt : mask.length = xs.length := by simpa using hx
              have hyt : mask.length = ys.length := by simpa using hy
              cases b
              · simp only [selected, Bool.false_eq_true, ↓reduceIte] at hh hl
                exact congrArg₂ List.cons (List.cons.inj hl).1
                  (ih xs ys hxt hyt hh (List.cons.inj hl).2)
              · simp only [selected, Bool.true_eq_false, ↓reduceIte] at hh hl
                exact congrArg₂ List.cons (List.cons.inj hh).1
                  (ih xs ys hxt hyt (List.cons.inj hh).2 hl)

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

end OAI.Algorithms
