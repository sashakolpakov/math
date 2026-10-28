import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgramRun

namespace OAI.Algorithms

/-! The factor dispatcher in the native leaf's actual bank.  The parsed ID
is retained for incidence preparation.  The mark flag is read from a tape,
not inserted as a program parameter. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 40 768
def register (i : Fin 8) : Fin 40 := i.castAdd 32
def stackMap : Fin 16 → Fin 768 :=
  ![701,700,152,704,705,340,341,342,343,344,345,346,347,348,349,154]

theorem register_injective : Function.Injective register := Fin.castAdd_injective 8 32
theorem stackMap_injective : Function.Injective stackMap := by decide

abbrev copyID : Cmd 40 768 := .call (StackRoutines.copyProgram 149 152 359 0 1)
abbrev readFlag : Cmd 40 768 := .base (.atom (.peek 706 7 0))
abbrev dispatch : Cmd 40 768 :=
  .call (ProgramLinking.liftProgram LeafFactorDispatchProgram.program register stackMap)
abbrev command : Cmd 40 768 := .seq (.seq copyID readFlag) dispatch

def scratch : List (Fin 768) := [152,154,340,341,342,343,344,345,346,347,348,349,359]
def copied (a : Data) : Data := afterCopy a 149 152 0 1
def staged (a : Data) : Data :=
  ⟨readRegs (copied a).regs 7 0 (a.stacks 706).head?,(copied a).stacks⟩

theorem stage_eval (a : Data) (hwork : a.stacks 359=[]) :
    Eval (.seq copyID readFlag) (7*(a.stacks 149).length+6) a (staged a) := by
  have hc := copy_eval a 149 152 359 0 1
    (by decide) (by decide) (by decide) (by decide) hwork
  have hp := Eval.base (StructuredProgram.Eval.atom
    (StructuredProgram.Atom.peek (706 : Fin 768) (7 : Fin 40) 0) (copied a))
  have he : (StructuredProgram.Atom.peek (706 : Fin 768) (7 : Fin 40) 0).eval
      (copied a)=staged a := by
    simp [staged,copied,afterCopy,StackRoutines.copyStacks,
      StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,execInstr]
  rw [he] at hp
  convert hc.seq hp using 1

noncomputable def finished (a : Data) (rf : Fin 8 → Bool)
    (rows clauses : List (List Bool)) (marked : Bool) (mark factor : ℕ) : Data :=
  embedState register stackMap (staged a)
    ⟨rf,LeafFactorDispatchProgram.outputStacks rows clauses marked mark factor⟩

theorem command_eval (a : Data) (rows clauses : List (List Bool))
    (marked : Bool) (mark factor : ℕ)
    (hrows : a.stacks 701=Encoding.encodeList id rows)
    (hclauses : a.stacks 700=Encoding.encodeList id clauses)
    (hcount : a.stacks 704=List.replicate rows.length true)
    (hmark : a.stacks 705=Encoding.encodeNat mark)
    (hflag : a.stacks 706=[marked])
    (hfactor : a.stacks 149=(Encoding.encodeNat factor).reverse)
    (hwork : ∀ i∈scratch, a.stacks i=[])
    (hvalid : marked=true → mark < clauses.length) :
    ∃ k rf, k ≤ 7*(a.stacks 149).length+6+
        LeafFactorDispatchProgram.budget rows clauses mark factor ∧
      Eval command k a (finished a rf rows clauses marked mark factor) ∧
      rf 5=decide (factor < rows.length) ∧
      rf 6=(marked && decide (factor=rows.length)) ∧ rf 7=marked := by
  obtain ⟨rf,h5,h6,h7,k,hk,he⟩ := LeafFactorDispatchProgram.program_runsIn
    ((staged a).regs ∘ register) rows clauses marked mark factor hvalid
  have hi : projectState register stackMap (staged a)=
      LeafFactorDispatchProgram.input ((staged a).regs ∘ register)
        rows clauses marked mark factor := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;>
        simp [staged,register,readRegs,hflag]
    · funext i
      fin_cases i <;>
        simp_all [stackMap,LeafFactorDispatchProgram.input,
          LeafFactorDispatchProgram.baseStacks,LeafFactorDispatchProgram.unary,
          staged,copied,afterCopy,StackRoutines.copyStacks,scratch]
  rw [← hi] at he
  have hd := eval_call_from_state LeafFactorDispatchProgram.program register stackMap
    (staged a) register_injective stackMap_injective he
  have hs := stage_eval a (hwork 359 (by simp [scratch]))
  exact ⟨_,rf,by omega,hs.seq hd,h5,h6,h7⟩

theorem finished_payload (a : Data) (rf : Fin 8 → Bool)
    (rows clauses : List (List Bool)) (marked : Bool) (mark factor : ℕ) :
    (finished a rf rows clauses marked mark factor).stacks 154=
      LeafFactorDispatchProgram.selectedPayload rows clauses marked mark factor := by
  change (finished a rf rows clauses marked mark factor).stacks (stackMap 15)=_
  simpa [finished, LeafFactorDispatchProgram.outputStacks] using
    (embedState_stack register stackMap (staged a)
      (⟨rf,LeafFactorDispatchProgram.outputStacks rows clauses marked mark factor⟩ :
        LeafFactorDispatchProgram.Data) stackMap_injective 15)

theorem finished_id (a : Data) (rf : Fin 8 → Bool)
    (rows clauses : List (List Bool)) (marked : Bool) (mark factor : ℕ) :
    (finished a rf rows clauses marked mark factor).stacks 149=a.stacks 149 := by
  rw [show (finished a rf rows clauses marked mark factor).stacks 149=
      (staged a).stacks 149 from
    embedState_stack_frame register stackMap (staged a) _ 149 (by decide)]
  simp [staged,copied,afterCopy,StackRoutines.copyStacks]

end SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch

end OAI.Algorithms
