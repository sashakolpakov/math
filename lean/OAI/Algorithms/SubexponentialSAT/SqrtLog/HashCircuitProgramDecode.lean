import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramLookup

namespace OAI.Algorithms

/-! Native conversion from the audited unary literal code `2*v+polarity` to
variable-key/polarity syntax. The source is a reversed parsed `encodeNat` record.
The loop consumes two unary marks per variable mark and records an odd tail as
positive polarity. Its instruction table is independent of the variable index. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

namespace Decode
abbrev Data := State 4 2

def data (value present positive : Bool) (src dst : List Bool) : Data :=
  ⟨![value,present,true,positive], ![src,dst]⟩

abbrev atom (a : StructuredProgram.Atom 4 2) : Cmd 4 2 := .base (.atom a)

abbrev pairBody : Cmd 4 2 :=
  .seq (atom (.pop 0 0 1))
    (.ite 1 (.seq (atom (.push 1 2)) (atom (.pop 0 0 1))) (atom (.set 3 true)))
abbrev pairLoop : Cmd 4 2 := .while 1 pairBody

def ready (m : ℕ) (acc : List Bool) : Data :=
  match m with
  | 0 => data false false false [] acc
  | m+1 => data true true false (List.replicate m true) acc

private theorem pop_cons (v pr p b : Bool) (xs acc : List Bool) :
    Eval (atom (.pop 0 0 1)) 1 (data v pr p (b::xs) acc) (data b true p xs acc) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.pop (0 : Fin 2) (0 : Fin 4) 1)
    (data v pr p (b::xs) acc))) using 1
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> simp [data,StructuredProgram.Atom.instr,execInstr,readRegs]
  · funext i; fin_cases i <;> simp [data,StructuredProgram.Atom.instr,execInstr]

private theorem pop_nil (v pr p : Bool) (acc : List Bool) :
    Eval (atom (.pop 0 0 1)) 1 (data v pr p [] acc) (data false false p [] acc) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.pop (0 : Fin 2) (0 : Fin 4) 1)
    (data v pr p [] acc))) using 1
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> simp [data,StructuredProgram.Atom.instr,execInstr,readRegs]
  · funext i; fin_cases i <;> simp [data,StructuredProgram.Atom.instr,execInstr]

private theorem push_acc (v pr p : Bool) (xs acc : List Bool) :
    Eval (atom (.push 1 2)) 1 (data v pr p xs acc) (data v pr p xs (true::acc)) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.push (1 : Fin 2) (2 : Fin 4))
    (data v pr p xs acc))) using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [data,StructuredProgram.Atom.instr,execInstr]

private theorem set_positive (v pr p : Bool) (xs acc : List Bool) :
    Eval (atom (.set 3 true)) 1 (data v pr p xs acc) (data v pr true xs acc) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.set (3 : Fin 4) true)
    (data v pr p xs acc))) using 1
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> simp [data,StructuredProgram.Atom.instr,execInstr]
  · rfl

private theorem body_pair (m : ℕ) (acc : List Bool) :
    Eval pairBody 4 (data true true false (true :: List.replicate m true) acc)
      (ready m (true::acc)) := by
  have h1 := pop_cons true true false true (List.replicate m true) acc
  have h2 := push_acc true true false (List.replicate m true) acc
  have h3 : Eval (atom (.pop 0 0 1)) 1
      (data true true false (List.replicate m true) (true::acc)) (ready m (true::acc)) := by
    cases m with
    | zero => exact pop_nil true true false _
    | succ m => simpa only [List.replicate_succ,ready] using
        (pop_cons true true false true (List.replicate m true) (true::acc))
  exact h1.seq (Eval.ite_true rfl (h2.seq h3))

private theorem body_odd (acc : List Bool) :
    Eval pairBody 3 (data true true false [] acc) (data false false true [] acc) := by
  exact (pop_nil true true false acc).seq (Eval.ite_false rfl (set_positive false false false [] acc))

theorem pairLoop_eval (v : ℕ) (positive : Bool) (acc : List Bool) :
    Eval pairLoop (5*v + 4*(if positive then 1 else 0) + 1)
      (ready (2*v + (if positive then 1 else 0)) acc)
      (data false false positive [] (List.replicate v true ++ acc)) := by
  induction v generalizing acc with
  | zero =>
    cases positive with
    | false => exact Eval.while_false rfl
    | true =>
      have ht : Eval pairLoop (3+1+1) (data true true false [] acc)
          (data false false true [] acc) :=
        Eval.while_true rfl (body_odd acc) (Eval.while_false rfl)
      simpa [ready] using ht
  | succ v ih =>
    have hh := Eval.while_true (test := (1 : Fin 4)) (body := pairBody) rfl
      (body_pair (2*v + (if positive then 1 else 0)) acc) (ih (true::acc))
    convert hh using 1
    · omega
    · rw [show 2*(v+1)+(if positive then 1 else 0) =
        (2*v+(if positive then 1 else 0))+2 by omega]
      simp [ready,List.replicate_succ]
    · simp only [List.replicate_succ]
      congr 1
      have h := List.replicate_add v 1 true
      simpa [List.replicate_succ, Nat.add_comm, List.append_assoc] using congrArg (· ++ acc) h

abbrev prepare : Cmd 4 2 :=
  .seq (atom (.pop 0 0 1))
    (.seq (atom (.set 2 true)) (.seq (atom (.set 3 false)) (atom (.pop 0 0 1))))

def input (regs : Fin 4 → Bool) (m : ℕ) : Data :=
  ⟨regs, ![(Encoding.encodeNat m).reverse, []]⟩

theorem prepare_eval (regs : Fin 4 → Bool) (m : ℕ) :
    Eval prepare 4 (input regs m) (ready m []) := by
  let a := (StructuredProgram.Atom.pop (0 : Fin 2) (0 : Fin 4) 1).eval (input regs m)
  let b := (StructuredProgram.Atom.set (2 : Fin 4) true).eval a
  let c := (StructuredProgram.Atom.set (3 : Fin 4) false).eval b
  have h1 : Eval (atom (.pop 0 0 1)) 1 (input regs m) a := .base (.atom _ _)
  have h2 : Eval (atom (.set 2 true)) 1 a b := .base (.atom _ _)
  have h3 : Eval (atom (.set 3 false)) 1 b c := .base (.atom _ _)
  have hc : c = data false true false (List.replicate m true) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [b,a,input,Encoding.encodeNat,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
        execInstr,readRegs]
    · funext i; fin_cases i <;> simp [b,a,input,Encoding.encodeNat,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
        execInstr]
  have h4 : Eval (atom (.pop 0 0 1)) 1 c (ready m []) := by
    rw [hc]
    cases m with
    | zero => exact pop_nil false true false []
    | succ m => simpa only [List.replicate_succ,ready] using
        (pop_cons false true false true (List.replicate m true) [])
  exact h1.seq (h2.seq (h3.seq h4))

abbrev emit : Cmd 4 2 :=
  .seq (.call (StackRoutines.transferProgram (1 : Fin 2) 0 (0 : Fin 4) 1))
    (.seq (atom (.set 0 false)) (.seq (atom (.push 0 0)) (atom (.push 0 3))))

def output (positive : Bool) (v : ℕ) : Data :=
  data false false positive ((Encoding.encodeNat v ++ [positive]).reverse) []

theorem emit_eval (positive : Bool) (v : ℕ) :
    Eval emit (3*v+6)
      (data false false positive [] (List.replicate v true)) (output positive v) := by
  let d := data false false positive [] (List.replicate v true)
  have h := StackRoutines.transferProgram_trace (1 : Fin 2) 0 (0 : Fin 4) 1
    (by decide) (by decide) d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 3 rfl rfl
  have ht : Eval (.call (StackRoutines.transferProgram (1 : Fin 2) 0 (0 : Fin 4) 1))
      (3*v+3) d (data false false positive (List.replicate v true) []) := by
    apply Eval.call
    have hr : readRegs d.regs 0 1 none = (data false false positive (List.replicate v true) []).regs := by
      funext i; fin_cases i <;> simp [d,data,readRegs]
    have hs : StackRoutines.transferStacks (1 : Fin 2) 0 d.stacks =
        (data false false positive (List.replicate v true) []).stacks := by
      funext i; fin_cases i <;> simp [d,data,StackRoutines.transferStacks]
    simp only [StackRoutines.transferResult] at hh
    rw [hr,hs] at hh
    simpa [StackRoutines.transferProgram,StructuredProgram.State.withPC,
      d,data,Nat.add_assoc] using hh
  let a := (StructuredProgram.Atom.set (0 : Fin 4) false).eval
    (data false false positive (List.replicate v true) [])
  let b := (StructuredProgram.Atom.push (0 : Fin 2) (0 : Fin 4)).eval a
  let c := (StructuredProgram.Atom.push (0 : Fin 2) (3 : Fin 4)).eval b
  have h1 : Eval (atom (.set 0 false)) 1 (data false false positive (List.replicate v true) []) a :=
    .base (.atom _ _)
  have h2 : Eval (atom (.push 0 0)) 1 a b := .base (.atom _ _)
  have h3 : Eval (atom (.push 0 3)) 1 b c := .base (.atom _ _)
  have hc : c = output positive v := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [b,a,data,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr]
    · funext i; fin_cases i <;> simp [b,a,data,Encoding.encodeNat,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr]
  rw [hc] at h3
  simpa [Nat.add_assoc] using ht.seq (h1.seq (h2.seq h3))

abbrev programCommand : Cmd 4 2 := .seq prepare (.seq pairLoop emit)
def program := compiled programCommand 0 0

theorem command_eval (regs : Fin 4 → Bool) (v : ℕ) (positive : Bool) :
    Eval programCommand (8*v + 4*(if positive then 1 else 0) + 11)
      (input regs (2*v + (if positive then 1 else 0))) (output positive v) := by
  have hp := prepare_eval regs (2*v + (if positive then 1 else 0))
  have hl := pairLoop_eval v positive []
  simp only [List.append_nil] at hl
  have he := emit_eval positive v
  convert hp.seq (hl.seq he) using 1 ; omega

theorem program_runs (regs : Fin 4 → Bool) (v : ℕ) (positive : Bool) :
    RunsIn program (8*v + 4*(if positive then 1 else 0) + 12)
      ((input regs (2*v + (if positive then 1 else 0))).withPC (some program.entry))
      ((output positive v).withPC none) := by
  have he := command_eval regs v positive
  exact ⟨_,by omega,compiled_halt_trace he 0 0⟩
end Decode
end SubexponentialSAT.SqrtLog.HashCircuitProgram

end OAI.Algorithms
