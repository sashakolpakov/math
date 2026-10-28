import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramParser
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Actual signed-pair framing, with every unrelated stack preserved. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram.Entries
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev EmitData := State 3 6

def emitPorts (negative : Bool) : Fin 4 → Fin 6 :=
  if negative then ![3,4,2,1] else ![3,4,2,0]

theorem emitPorts_injective (negative : Bool) : Function.Injective (emitPorts negative) := by
  cases negative <;> decide

abbrev emitOne (negative : Bool) : Cmd 3 6 :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.emitRecordProgram id
    (emitPorts negative))

def emitOneStacks (negative : Bool) (d : EmitData) : Fin 6 → List Bool :=
  Function.update (Function.update d.stacks (if negative then 1 else 0) []) 2
    (true :: (Encoding.frame (d.stacks (if negative then 1 else 0)).reverse ++ d.stacks 2))

theorem emitOne_eval (negative : Bool) (d : EmitData) :
    ∃ e : EmitData,
      Eval (emitOne negative) (5*(d.stacks (if negative then 1 else 0)).length+7) d e ∧
      e.stacks = emitOneStacks negative d := by
  let a := projectState id (emitPorts negative) d
  let bits := (d.stacks (if negative then 1 else 0)).reverse
  have ha : SubexpNormalizeProgram.filterState (d.regs 0) (d.regs 1) (d.regs 2)
      (d.stacks 3) (d.stacks 4) (d.stacks 2) bits.reverse = a := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j; fin_cases j <;> rfl
    · funext j; cases negative <;> fin_cases j <;> simp [ bits, emitPorts,
        SubexpPostfixControl.quadruple]
  let b := SubexpNormalizeProgram.filterState true false (d.regs 2)
    (d.stacks 3) (d.stacks 4) (true :: (Encoding.frame bits ++ d.stacks 2)) []
  have ht := SubexpNormalizeProgram.emitRecord_trace bits (d.stacks 3) (d.stacks 4)
    (d.stacks 2) (d.regs 0) (d.regs 1) (d.regs 2)
  rw [ha] at ht
  have he := eval_call_lifted SubexpNormalizeProgram.emitRecordProgram id
    (emitPorts negative) d Function.injective_id (emitPorts_injective negative) ht
  rw [embedState_project id (emitPorts negative) d Function.injective_id
    (emitPorts_injective negative)] at he
  refine ⟨embedState id (emitPorts negative) d b, ?_, ?_⟩
  · simpa only [emitOne, bits, List.length_reverse] using he
  · have hbs : b.stacks = Function.update (Function.update a.stacks 3 []) 2
        (true :: (Encoding.frame bits ++ d.stacks 2)) := by
      funext i
      cases negative <;> fin_cases i <;> simp [b,a,projectState,emitPorts,
        SubexpNormalizeProgram.filterState,SubexpPostfixControl.quadruple]
    change Function.extend (emitPorts negative) b.stacks d.stacks = _
    rw [hbs, ProgramLinking.extend_update (emitPorts_injective negative),
      ProgramLinking.extend_update (emitPorts_injective negative)]
    have hbase := congrArg StructuredProgram.State.stacks
      (embedState_project id (emitPorts negative) d Function.injective_id
        (emitPorts_injective negative))
    change Function.extend (emitPorts negative) a.stacks d.stacks = d.stacks at hbase
    rw [hbase]
    cases negative <;> rfl

/-- Prepend a positive and negative frame with one outer pair tag. Inputs 0,1
are consumed; output 2 is extended; ports 3--5 are preserved. -/
abbrev emitPair : Cmd 3 6 :=
  .seq (emitOne true) (.seq (.base (.atom (.pop 2 0 1))) (emitOne false))

def pairPrefix (p n : List Bool) : List Bool :=
  true :: (Encoding.frame p.reverse ++ Encoding.frame n.reverse)

theorem emitPair_eval (d : EmitData) :
    ∃ e : EmitData,
      Eval emitPair (5*((d.stacks 0).length+(d.stacks 1).length)+15) d e ∧
      e.stacks = Function.update (Function.update (Function.update d.stacks 0 []) 1 []) 2
        (pairPrefix (d.stacks 0) (d.stacks 1) ++ d.stacks 2) := by
  obtain ⟨a, ha, has⟩ := emitOne_eval true d
  let b := (StructuredProgram.Atom.pop 2 0 1).eval a
  have hb : Eval (.base (.atom (.pop 2 0 1))) 1 a b := .base (.atom _ _)
  have hbs : b.stacks = Function.update (Function.update d.stacks 1 []) 2
      (Encoding.frame (d.stacks 1).reverse ++ d.stacks 2) := by
    funext j
    simp [b, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr,
      has, emitOneStacks, Function.update_apply]
  obtain ⟨e, he, hes⟩ := emitOne_eval false b
  refine ⟨e, ?_, ?_⟩
  · have hh := ha.seq (hb.seq he)
    convert hh using 1 ; simp [ hbs ] ; omega
  · rw [hes, emitOneStacks, hbs]
    funext j
    by_cases h0 : j=0 <;> by_cases h1 : j=1 <;> by_cases h2 : j=2 <;>
      simp_all [pairPrefix, List.append_assoc, Function.update_apply]

@[simp] theorem pairPrefix_cons (p : WordPair) (xs : List WordPair) :
    pairPrefix p.1 p.2 ++ pairEncoding xs = pairEncoding (p::xs) := by
  simp [pairPrefix, pairEncoding, List.append_assoc]

end SubexponentialSAT.SqrtLog.RowSelectionProgram.Entries

end OAI.Algorithms
