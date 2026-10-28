import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramSelectData

namespace OAI.Algorithms

/-! Fixed framing primitive for the scored-record writer. It consumes the
input bits and prepends the frame of their reversal to the output stack. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgramSelect

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev FrameData := State 3 2

abbrev frameState (v p : Bool) (input output : List Bool) : FrameData :=
  ⟨![v,p,true], ![input,output]⟩

abbrev framePopped : List Bool → List Bool → FrameData
  | [], out => frameState false false [] out
  | b::bs, out => frameState b true bs out

def frameOutput (bits out : List Bool) : List Bool :=
  bits.reverse.flatMap (fun b => [true,b]) ++ out

abbrev frameAtom (a : StructuredProgram.Atom 3 2) : Cmd 3 2 := .base (.atom a)

abbrev frameBody : Cmd 3 2 :=
  .seq (frameAtom (.push 1 0))
    (.seq (frameAtom (.push 1 2)) (frameAtom (.pop 0 0 1)))

abbrev frameLoop : Cmd 3 2 := .while 1 frameBody

theorem frameBody_eval (b : Bool) (bs out : List Bool) :
    Eval frameBody 3 (framePopped (b::bs) out) (framePopped bs (true::b::out)) := by
  let d := framePopped (b::bs) out
  let d1 := (StructuredProgram.Atom.push (1 : Fin 2) (0 : Fin 3)).eval d
  let d2 := (StructuredProgram.Atom.push (1 : Fin 2) (2 : Fin 3)).eval d1
  have h1 := Eval.base (StructuredProgram.Eval.atom (.push 1 0) d)
  have h2 := Eval.base (StructuredProgram.Eval.atom (.push 1 2) d1)
  have h3 := Eval.base (StructuredProgram.Eval.atom (.pop 0 0 1) d2)
  convert h1.seq (h2.seq h3) using 1
  cases bs <;>
    simp [d2,d1,d,framePopped,frameState,StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr,readRegs] <;>
    constructor <;> funext i <;> fin_cases i <;> simp

theorem frameLoop_eval (bits out : List Bool) :
    Eval frameLoop (4*bits.length+1) (framePopped bits out)
      (frameState false false [] (frameOutput bits out)) := by
  induction bits generalizing out with
  | nil => exact Eval.while_false rfl
  | cons b bs ih =>
    have h := Eval.while_true (show (framePopped (b::bs) out).regs 1 = true from rfl)
      (frameBody_eval b bs out) (ih (true::b::out))
    convert h using 1 <;>
      simp [frameOutput,List.reverse_cons,List.flatMap_append,List.append_assoc] ; omega

abbrev frameCommand : Cmd 3 2 :=
  .seq (frameAtom (.set 2 false))
    (.seq (frameAtom (.push 1 2))
      (.seq (frameAtom (.set 2 true))
        (.seq (frameAtom (.pop 0 0 1)) frameLoop)))

abbrev frameProgram := compiled frameCommand 0 1

theorem frameOutput_frame (bits out : List Bool) :
    frameOutput bits (false::out) = Encoding.frame bits.reverse ++ out := by
  have h (xs : List Bool) :
      xs.flatMap (fun b => [true,b]) ++ (false::out) = Encoding.frame xs ++ out := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simpa [Encoding.frame] using congrArg (fun ys => true::x::ys) ih
  exact h bits.reverse

theorem frameCommand_eval (regs : Fin 3 → Bool) (bits out : List Bool) :
    Eval frameCommand (4*bits.length+5) ⟨regs,![bits,out]⟩
      (frameState false false [] (Encoding.frame bits.reverse ++ out)) := by
  let d : FrameData := ⟨regs,![bits,out]⟩
  let d1 := (StructuredProgram.Atom.set (2 : Fin 3) false).eval d
  let d2 := (StructuredProgram.Atom.push (1 : Fin 2) (2 : Fin 3)).eval d1
  let d3 := (StructuredProgram.Atom.set (2 : Fin 3) true).eval d2
  let d4 := (StructuredProgram.Atom.pop (0 : Fin 2) (0 : Fin 3) 1).eval d3
  have hd4 : d4 = framePopped bits (false::out) := by
    cases bits <;>
      simp [d4,d3,d2,d1,d,framePopped,frameState,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr,readRegs] <;>
    constructor <;> funext i <;> fin_cases i <;> simp
  have hl := frameLoop_eval bits (false::out)
  rw [frameOutput_frame, ←hd4] at hl
  have h1 := Eval.base (StructuredProgram.Eval.atom (.set 2 false) d)
  have h2 := Eval.base (StructuredProgram.Eval.atom (.push 1 2) d1)
  have h3 := Eval.base (StructuredProgram.Eval.atom (.set 2 true) d2)
  have h4 := Eval.base (StructuredProgram.Eval.atom (.pop 0 0 1) d3)
  convert h1.seq (h2.seq (h3.seq (h4.seq hl))) using 1 ; omega

theorem frameProgram_trace (regs : Fin 3 → Bool) (bits out : List Bool) :
    Trace frameProgram (4*bits.length+6)
      ((⟨regs,![bits,out]⟩ : FrameData).withPC (some frameProgram.entry))
      ((frameState false false [] (Encoding.frame bits.reverse ++ out)).withPC none) := by
  convert compiled_halt_trace (frameCommand_eval regs bits out) 0 1 using 1

end SubexponentialSAT.SqrtLog.RowSelectionProgramSelect

end OAI.Algorithms
