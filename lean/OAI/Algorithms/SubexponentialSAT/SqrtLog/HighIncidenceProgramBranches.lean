import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram
import OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration
import OAI.Algorithms.SubexponentialSAT.Subexp.UnaryTally

namespace OAI.Algorithms

/-! Runtime Boolean branch initialization and exhaustive odometer traces.
The only parameter in the enumeration command is its fixed real callback.
The high dimension is data, not finite control. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 2 2
abbrev Code := Cmd 2 2
abbrev trueCount := Subexp.PaddedCompletion.trueCount

def state (regs : Fin 2 → Bool) (mask out : List Bool) : Data := ⟨regs, ![mask, out]⟩
@[simp] theorem update_out (a b c : List Bool) :
    Function.update (![a, b] : Fin 2 → List Bool) 1 c = ![a, c] := by
  funext i; fin_cases i <;> rfl
@[simp] theorem update_input (a b c : List Bool) :
    Function.update (![a, b] : Fin 2 → List Bool) 0 c = ![c, b] := by
  funext i; fin_cases i <;> rfl

def push (b : Bool) : Code := .seq (.base (.atom (.set 0 b))) (.base (.atom (.push 1 0)))
def pushed (b : Bool) (a : Data) : Data :=
  ⟨Function.update a.regs 0 b, Function.update a.stacks 1 (b :: a.stacks 1)⟩
theorem push_eval (b : Bool) (a : Data) : Eval (push b) 2 a (pushed b a) := by
  have h := (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 2) b) a)).seq
    (Eval.base (StructuredProgram.Eval.atom (.push (1 : Fin 2) 0) _))
  simpa [push, pushed, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using h

def record : Code := .seq (push false) (.seq (push false) (.seq (push true) (push true)))
theorem record_eval (regs : Fin 2 → Bool) (mask out : List Bool) :
    Eval record 8 (state regs mask out)
      (state (Function.update regs 0 true) mask (true :: true :: false :: false :: out)) := by
  let a := state regs mask out
  have h := (push_eval false a).seq ((push_eval false (pushed false a)).seq
    ((push_eval true (pushed false (pushed false a))).seq
      (push_eval true (pushed true (pushed false (pushed false a))))))
  simpa [record, pushed, a, state, Function.update_idem] using h

def pop : Code := .base (.atom (.pop 0 0 1))
def popped (regs : Fin 2 → Bool) (mask out : List Bool) : Data :=
  state (readRegs regs 0 1 mask.head?) mask.tail out

theorem pop_eval (regs : Fin 2 → Bool) (mask out : List Bool) :
    Eval pop 1 (state regs mask out) (popped regs mask out) := by
  simpa [pop, state, popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using
    (Eval.base (StructuredProgram.Eval.atom (.pop (0 : Fin 2) 0 1) (state regs mask out)))

def loop : Code := .while 1 (.seq (.ite 0 record (.base .skip)) pop)
def command : Code := .seq (push false) (.seq pop loop)

def prepend : ℕ → List Bool → List Bool
  | 0, out => out
  | h+1, out => true :: true :: false :: false :: prepend h out

theorem prepend_step (h : ℕ) (out : List Bool) :
    prepend h (true :: true :: false :: false :: out) = prepend (h+1) out := by
  induction h <;> simp [prepend, *]

theorem loop_eval (regs : Fin 2 → Bool) (mask out : List Bool) :
    ∃ rf, Eval loop (3 * mask.length + 8 * trueCount mask + 1)
      (popped regs mask out) (state rf [] (prepend (trueCount mask) out)) := by
  induction mask generalizing regs out with
  | nil => exact ⟨readRegs regs 0 1 none, Eval.while_false (by rfl)⟩
  | cons b mask ih =>
      cases b with
      | false =>
          let r := readRegs regs 0 1 (some false)
          obtain ⟨rf, hr⟩ := ih r out
          have hs : Eval (.ite (0 : Fin 2) record (.base .skip)) 1
              (state r mask out) (state r mask out) := .ite_false (by rfl) (.base (.skip _))
          have h := Eval.while_true (by rfl : (popped regs (false :: mask) out).regs 1 = true)
            (hs.seq (pop_eval r mask out)) hr
          refine ⟨rf, ?_⟩
          convert h using 1 <;> simp [loop, trueCount, Subexp.PaddedCompletion.trueCount,
            Subexp.PaddedCompletion.successful, Nat.mul_add, Nat.add_assoc] ; omega
      | true =>
          let r := readRegs regs 0 1 (some true)
          let r' := Function.update r 0 true
          obtain ⟨rf, hr⟩ := ih r' (true :: true :: false :: false :: out)
          have hs : Eval (.ite (0 : Fin 2) record (.base .skip)) 9
              (state r mask out) (state r' mask (true :: true :: false :: false :: out)) :=
            .ite_true (by rfl) (record_eval r mask out)
          have h := Eval.while_true (by rfl : (popped regs (true :: mask) out).regs 1 = true)
            (hs.seq (pop_eval r' mask (true :: true :: false :: false :: out))) hr
          refine ⟨rf, ?_⟩
          convert h using 1 <;> simp [loop, trueCount, Subexp.PaddedCompletion.trueCount,
            Subexp.PaddedCompletion.successful, prepend_step, Nat.mul_add,
            Nat.add_assoc, Nat.add_comm ] ; omega

theorem prepend_encode (h : ℕ) :
    prepend h [false] = Encoding.encodeList id (List.replicate h [false]) := by
  induction h <;> simp [prepend, List.replicate_succ, Encoding.encodeList, Encoding.frame, *]

theorem command_eval (regs : Fin 2 → Bool) (mask : List Bool) :
    ∃ rf, Eval command (3 * mask.length + 8 * trueCount mask + 4)
      (state regs mask [])
      (state rf [] (Encoding.encodeList id (List.replicate (trueCount mask) [false]))) := by
  let r := Function.update regs 0 false
  have hp := push_eval false (state regs mask [])
  have hp' : Eval (push false) 2 (state regs mask []) (state r mask [false]) := by
    simpa [r, state, pushed] using hp
  obtain ⟨rf, hr⟩ := loop_eval r mask [false]
  refine ⟨rf, ?_⟩
  convert hp'.seq ((pop_eval r mask [false]).seq hr) using 1 <;>
    (try simp only [command, prepend_encode]) ; omega

def program := compiled command 0 1

theorem program_runsIn (regs : Fin 2 → Bool) (mask : List Bool) :
    ∃ rf, RunsIn program (11 * mask.length + 5)
      ((state regs mask []).withPC (some program.entry))
      ((state rf [] (Encoding.encodeList id (List.replicate (trueCount mask) [false]))).withPC none) := by
  obtain ⟨rf, he⟩ := command_eval regs mask
  have hc : trueCount mask ≤ mask.length := List.length_filter_le id mask
  exact ⟨rf, _, by omega, compiled_halt_trace he 0 1⟩

section Enumerate
variable {R S : ℕ}

/-- The initialized one-bit records enumerate exactly all assignments to the
selected coordinates. Every callback is an actual trace; rejected branches
remain in the cost and in the visit log. -/
theorem enumerate_high (p : CounterForPrograms.Ports R S) (body : Cmd R S)
    (I : State R S → Prop) (budget h : ℕ)
    (stable : CounterForPrograms.FrameStable p (fun _ => I))
    (spec : ExecCNFTupleEnumeration.BodySpec p body (List.replicate h 1) I budget)
    (a : State R S) (hi : I a)
    (hc : a.stacks p.counter = Encoding.encodeList id (List.replicate h [false]))
    (hs : a.stacks p.scratch = []) :
    ∃ time b, Eval (ExecCNFTupleEnumeration.enumerate p body) (1+time) a b ∧
      ExecCNFTupleEnumeration.Visits p body (List.replicate h 1)
        (List.range' 0 (2^h)) time (ExecCNFTupleEnumeration.startResult p a) b ∧
      I b ∧ b.stacks p.scratch = [] ∧
      1+time ≤ 2^h * (budget + 28*h + 12) + 2 := by
  obtain ⟨time, b, he, hv, hib, hf, hsb, ht⟩ :=
    ExecCNFTupleEnumeration.enumerate_correct p body (List.replicate h 1) I budget
      stable spec (List.replicate h [false]) a (by simp) hi hc hs (by simp)
  have hlen : (List.replicate h [false]).flatten.length = h := by simp
  have henc : (Encoding.encodeList id (List.replicate h [false])).length = 4*h+1 := by
    rw [ExecCNFTupleOdometer.encoded_length, hlen, List.length_replicate]
    omega
  rw [hlen, henc] at ht
  rw [hlen] at hv
  exact ⟨time, b, he, hv, hib, hsb, by nlinarith⟩

/-- Every h-bit high assignment has its own actual callback invocation. -/
theorem covers_high_assignment {p : CounterForPrograms.Ports R S} {body : Cmd R S}
    {h time : ℕ} {a b : State R S}
    (hv : ExecCNFTupleEnumeration.Visits p body (List.replicate h 1)
      (List.range' 0 (2^h)) time a b)
    (bits : List Bool) (hlen : bits.length = h) :
    ∃ x y cost, x.stacks p.counter = Encoding.encodeList id (bits.map (fun b => [b])) ∧
      Eval body cost x y := by
  apply ExecCNFTupleEnumeration.Visits.covers (shape := List.replicate h 1)
    (n := time) (d := a) (e := b) (by simpa using hv)
  simp [List.map_map, Function.comp_def, hlen]

end Enumerate

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches

end OAI.Algorithms
