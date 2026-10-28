import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramCell
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

/-! Fixed native operations for adding a Cayley shift to a vertex word.
The Boolean mode chooses left or right incidence; shift frames are consumed
on both sides so each iteration advances exactly one local port. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 8 4

def state (regs : Fin 8 → Bool) (source vertex accum out : List Bool) : Data :=
  ⟨regs,![source,vertex,accum,out]⟩
def frames (bits : List Bool) : List Bool := bits.flatMap fun b => Cell.frame b false

def cellRegisters : Fin 4 → Fin 8 := Fin.castAdd 4
def cellStacks (_ : Fin 1) : Fin 4 := 0
abbrev cell : Cmd 8 4 := .call (ProgramLinking.liftProgram Cell.program cellRegisters cellStacks)

def cellRegs (regs : Fin 8 → Bool) (b : Bool) : Fin 8 → Bool :=
  ![false,true,b,false,regs 4,regs 5,regs 6,regs 7]

theorem cellRegisters_injective : Function.Injective cellRegisters := Fin.castAdd_injective _ _
theorem cellStacks_injective : Function.Injective cellStacks := by intro i j h; fin_cases i; fin_cases j; rfl

theorem cell_eval (regs : Fin 8 → Bool) (b : Bool) (tail vertex accum out : List Bool) :
    Eval cell 6 (state regs (Cell.frame b false++tail) vertex accum out)
      (state (cellRegs regs b) tail vertex accum out) := by
  let d := state regs (Cell.frame b false++tail) vertex accum out
  have hs : embedState cellRegisters cellStacks d
      (Cell.state (regs ∘ cellRegisters) (Cell.frame b false++tail))=d := by
    apply embedState_eq_of_ports _ _ _ _ _ cellRegisters_injective cellStacks_injective
    · intro i; rfl
    · intro i hi; rfl
    · intro i; fin_cases i; rfl
    · intro i hi; rfl
  have hf : embedState cellRegisters cellStacks d
      (Cell.state ![false,true,b,false] tail)=state (cellRegs regs b) tail vertex accum out := by
    apply embedState_eq_of_ports _ _ _ _ _ cellRegisters_injective cellStacks_injective
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h0 : i≠0 := fun h => hi ⟨0,by simpa [cellRegisters] using h.symm⟩
      have h1 : i≠1 := fun h => hi ⟨1,by simpa [cellRegisters] using h.symm⟩
      have h2 : i≠2 := fun h => hi ⟨2,by simpa [cellRegisters] using h.symm⟩
      have h3 : i≠3 := fun h => hi ⟨3,by simpa [cellRegisters] using h.symm⟩
      fin_cases i <;> simp_all [cellRegs,state,d]
    · intro i; fin_cases i; rfl
    · intro i hi
      have h0 : i≠0 := fun h => hi ⟨0,by simpa [cellStacks] using h.symm⟩
      fin_cases i <;> simp_all [state,d]
  have he := eval_call_lifted Cell.program cellRegisters cellStacks d
    cellRegisters_injective cellStacks_injective (Cell.program_trace (regs ∘ cellRegisters) b false tail)
  rw [hs,hf] at he
  exact he

abbrev combine : Cmd 8 4 :=
  .ite 7 (.base (.atom (.bxor 4 4 2))) (.base (.atom (.copy 4 4)))

abbrev pop : Cmd 8 4 := .base (.atom (.pop 1 4 5))
abbrev step : Cmd 8 4 := .seq cell (.seq combine (.base (.atom (.push 2 4))))
abbrev loop : Cmd 8 4 := .seq pop (.while 5 (.seq step pop))
abbrev command : Cmd 8 4 := .seq loop (.call (StackRoutines.transferProgram 2 3 0 1))
def program := compiled command 0 3

def bit (side v shift : Bool) : Bool := if side then v.xor shift else v

theorem combine_eval (regs : Fin 8 → Bool) (side v shift : Bool)
    (hside : regs 7=side) (hv : regs 4=v) (hs : regs 2=shift)
    (source vertex accum out : List Bool) :
    Eval combine 2 (state regs source vertex accum out)
      (state (Function.update regs 4 (bit side v shift)) source vertex accum out) := by
  cases side
  · apply Eval.ite_false hside
    simpa [bit,hv,state,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr]
      using (Eval.base (StructuredProgram.Eval.atom (.copy 4 4)
      (state regs source vertex accum out)))
  · apply Eval.ite_true hside
    simpa [bit,hv,hs,state,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr]
      using (Eval.base (StructuredProgram.Eval.atom (.bxor 4 4 2)
      (state regs source vertex accum out)))

theorem step_eval (regs : Fin 8 → Bool) (side v shift : Bool)
    (hside : regs 7=side) (hv : regs 4=v)
    (tail vertex accum out : List Bool) :
    ∃ rf, rf 7=side ∧ Eval step 9
      (state regs (Cell.frame shift false++tail) vertex accum out)
      (state rf tail vertex (bit side v shift::accum) out) := by
  have h1 := cell_eval regs shift tail vertex accum out
  let r1 := cellRegs regs shift
  have h2 := combine_eval r1 side v shift hside hv rfl tail vertex accum out
  let r2 := Function.update r1 4 (bit side v shift)
  have h3 : Eval (.base (.atom (.push 2 4))) 1 (state r2 tail vertex accum out)
      (state r2 tail vertex (bit side v shift::accum) out) := by
    have hst : Function.update (![tail,vertex,accum,out] : Fin 4 → List Bool) 2
        (bit side v shift::accum)=![tail,vertex,bit side v shift::accum,out] := by
      funext i; fin_cases i <;> simp
    simpa [state,r2,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr,hst]
      using (Eval.base (StructuredProgram.Eval.atom (.push 2 4)
      (state r2 tail vertex accum out)))
  exact ⟨r2,by simp [r2,r1,cellRegs,hside],h1.seq (h2.seq h3)⟩

theorem pop_cons (regs : Fin 8 → Bool) (v : Bool) (source vertex accum out : List Bool) :
    Eval pop 1 (state regs source (v::vertex) accum out)
      (state (readRegs regs 4 5 (some v)) source vertex accum out) := by
  have hst : Function.update (![source,v::vertex,accum,out] : Fin 4 → List Bool) 1
      vertex=![source,vertex,accum,out] := by
    funext i; fin_cases i <;> simp
  simpa [state,pop,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr,hst]
    using (Eval.base (StructuredProgram.Eval.atom (.pop 1 4 5)
    (state regs source (v::vertex) accum out)))

theorem pop_nil (regs : Fin 8 → Bool) (source accum out : List Bool) :
    Eval pop 1 (state regs source [] accum out)
      (state (readRegs regs 4 5 none) source [] accum out) := by
  have hst : Function.update (![source,[],accum,out] : Fin 4 → List Bool) 1
      []=![source,[],accum,out] := by
    funext i; fin_cases i <;> simp
  simpa [state,pop,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr,hst]
    using (Eval.base (StructuredProgram.Eval.atom (.pop 1 4 5)
    (state regs source [] accum out)))

end SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift

end OAI.Algorithms
