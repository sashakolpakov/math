import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.BinaryArithmetic

namespace OAI.Algorithms

/-! A fixed bit program generates the power-of-two clearing denominator from
its unary exponent. The exponent is runtime data, never control-table size. -/

namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic

abbrev PowerData := State 2 2

abbrev powerRead : Cmd 2 2 := .base (.atom (.pop 0 0 1))
abbrev powerPutZero : Cmd 2 2 := .seq (.base (.atom (.set 0 false)))
  (.base (.atom (.push 1 0)))
abbrev powerLoop : Cmd 2 2 := .while 1 (.seq powerPutZero powerRead)
abbrev powerCommand : Cmd 2 2 :=
  .seq (.base (.atom (.set 0 true)))
    (.seq (.base (.atom (.push 1 0))) (.seq powerRead powerLoop))
def powerProgram := compiled powerCommand 0 1

def powerState (regs : Fin 2 → Bool) (counter output : List Bool) : PowerData :=
  ⟨regs, ![counter,output]⟩

def powerAfterRead (regs : Fin 2 → Bool) (counter output : List Bool) : PowerData :=
  powerState (readRegs regs 0 1 counter.head?) counter.tail output

private theorem powerRead_eval (regs : Fin 2 → Bool) (counter output : List Bool) :
    Eval powerRead 1 (powerState regs counter output) (powerAfterRead regs counter output) := by
  have h := Eval.base (SubexponentialSAT.StructuredProgram.Eval.atom
    (.pop (0 : Fin 2) (0 : Fin 2) 1) (powerState regs counter output))
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext j
    fin_cases j <;> simp [ powerState,
      StructuredProgram.Atom.instr, execInstr]

private theorem powerLoop_eval (regs : Fin 2 → Bool) (counter output : List Bool) :
    Eval powerLoop (4 * counter.length + 1) (powerAfterRead regs counter output)
      (powerState (readRegs regs 0 1 none) []
        (List.replicate counter.length false ++ output)) := by
  induction counter generalizing regs output with
  | nil =>
    simpa [powerLoop, powerAfterRead, powerState] using
      (Eval.while_false (test := (1 : Fin 2))
        (body := .seq powerPutZero powerRead)
        (a := powerAfterRead regs [] output)
        (by simp [powerAfterRead, powerState, readRegs_present]))
  | cons bit counter ih =>
    let r := readRegs regs 0 1 (some bit)
    let r0 := Function.update r 0 false
    have hs : Eval (.base (.atom (.set 0 false))) 1
        (powerState r counter output) (powerState r0 counter output) :=
      .base (.atom _ _)
    have hp : Eval (.base (.atom (.push 1 0))) 1
        (powerState r0 counter output) (powerState r0 counter (false :: output)) := by
      convert (Eval.base (SubexponentialSAT.StructuredProgram.Eval.atom
          (.push (1 : Fin 2) (0 : Fin 2)) (powerState r0 counter output))) using 1
      apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext j
        fin_cases j <;> simp [powerState, r0,
          StructuredProgram.Atom.instr, execInstr]
    have hr := powerRead_eval r0 counter (false :: output)
    have ht := ih r0 (false :: output)
    have he := Eval.while_true (test := (1 : Fin 2))
      (by simp [powerState, r, readRegs_present]) ((hs.seq hp).seq hr) ht
    have hreg : readRegs r0 0 1 none = readRegs regs 0 1 none := by
      funext j
      fin_cases j <;> simp [readRegs, r0, r]
    have hrp : List.replicate counter.length false ++ false :: output =
        false :: (List.replicate counter.length false ++ output) := by
      induction counter.length with
      | zero => rfl
      | succ n ih => simpa [List.replicate_succ] using congrArg (false :: ·) ih
    convert he using 1 <;>
      simp [ powerAfterRead, powerState, r,
        hreg, List.replicate_succ, hrp] ; omega

/-- The output is the little-endian word for 2^q, prepended to its old tail. -/
theorem powerCommand_eval (regs : Fin 2 → Bool) (counter output : List Bool) :
    Eval powerCommand (4 * counter.length + 4) (powerState regs counter output)
      (powerState (readRegs regs 0 1 none) []
        (List.replicate counter.length false ++ true :: output)) := by
  let r := Function.update regs 0 true
  have hs : Eval (.base (.atom (.set 0 true))) 1
      (powerState regs counter output) (powerState r counter output) :=
    .base (.atom _ _)
  have hp : Eval (.base (.atom (.push 1 0))) 1
      (powerState r counter output) (powerState r counter (true :: output)) := by
    convert (Eval.base (SubexponentialSAT.StructuredProgram.Eval.atom
        (.push (1 : Fin 2) (0 : Fin 2)) (powerState r counter output))) using 1
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;> simp [powerState, r,
        StructuredProgram.Atom.instr, execInstr]
  have hr := powerRead_eval r counter (true :: output)
  have hl := powerLoop_eval r counter (true :: output)
  have hreg : readRegs r 0 1 none = readRegs regs 0 1 none := by
    funext j
    fin_cases j <;> simp [readRegs, r]
  have h := hs.seq (hp.seq (hr.seq hl))
  convert h using 1 <;> first | omega | simp [ hreg]

theorem powerWord_value (q : ℕ) :
    BinaryArithmetic.toNat (List.replicate q false ++ [true]) = 2 ^ q := by
  induction q with
  | zero => simp [BinaryArithmetic.toNat, bitVal]
  | succ q ih => simp [List.replicate_succ, bitVal, ih, pow_succ, Nat.mul_comm]

theorem powerProgram_runsIn (regs : Fin 2 → Bool) (counter : List Bool) :
    RunsIn powerProgram (4 * counter.length + 5)
      ((powerState regs counter []).withPC (some powerProgram.entry))
      ((powerState (readRegs regs 0 1 none) []
        (List.replicate counter.length false ++ [true])).withPC none) := by
  refine ⟨_, ?_, compiled_halt_trace (powerCommand_eval regs counter []) 0 1⟩
  omega

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
