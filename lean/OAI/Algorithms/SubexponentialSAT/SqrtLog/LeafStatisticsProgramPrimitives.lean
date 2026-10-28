import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgramMax
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

namespace OAI.Algorithms

/-! Fixed-register local operations for the actual residual statistics scan. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Data := State 10 21
abbrev Code := Cmd 10 21
abbrev unary (n : ℕ) := List.replicate n true

def copy (src dst tmp : Fin 21) : Code :=
  .call (StackRoutines.copyProgram src dst tmp 0 1)
def copied (src dst : Fin 21) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks src dst a.stacks⟩
theorem copy_eval (src dst tmp : Fin 21) (a : Data)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (ht : a.stacks tmp = []) :
    Eval (copy src dst tmp) (7*(a.stacks src).length+5) a (copied src dst a) :=
  .call _ (ListRegisterProgram.copy_run src dst tmp 0 1 hsd hst htd (by decide) a.regs a.stacks ht)

def transfer (src dst : Fin 21) : Code :=
  .call (StackRoutines.transferProgram src dst 0 1)
def transferred (src dst : Fin 21) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.transferStacks src dst a.stacks⟩
theorem transfer_eval (src dst : Fin 21) (a : Data) (hsd : src ≠ dst) :
    Eval (transfer src dst) (3*(a.stacks src).length+3) a (transferred src dst a) :=
  .call _ (ListRegisterProgram.transfer_run src dst 0 1 hsd (by decide) a.regs a.stacks)

def pushTrue (dst : Fin 21) : Code :=
  .seq (.base (.atom (.set 0 true))) (.base (.atom (.push dst 0)))
def pushedTrue (dst : Fin 21) (a : Data) : Data :=
  ⟨Function.update a.regs 0 true, Function.update a.stacks dst (true::a.stacks dst)⟩
theorem pushTrue_eval (dst : Fin 21) (a : Data) : Eval (pushTrue dst) 2 a (pushedTrue dst a) := by
  have h := (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 10) true) a)).seq
    (Eval.base (StructuredProgram.Eval.atom (.push dst (0 : Fin 10)) _))
  simpa [pushTrue,pushedTrue,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr] using h

def pop (src : Fin 21) : Code := .base (.atom (.pop src 0 1))
def popped (src : Fin 21) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 (a.stacks src).head?, Function.update a.stacks src (a.stacks src).tail⟩
theorem pop_eval (src : Fin 21) (a : Data) : Eval (pop src) 1 a (popped src a) := .base (.atom _ _)

def peek (src : Fin 21) : Code := .base (.atom (.peek src 0 1))
def peeked (src : Fin 21) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 (a.stacks src).head?,a.stacks⟩
theorem peek_eval (src : Fin 21) (a : Data) : Eval (peek src) 1 a (peeked src a) := .base (.atom _ _)

def maxRegs : Fin 3 → Fin 10 := Fin.castAdd 7
def maxStacks : Fin 3 → Fin 21 := ![18,15,19]
theorem maxRegs_injective : Function.Injective maxRegs := Fin.castAdd_injective _ _
theorem maxStacks_injective : Function.Injective maxStacks := by decide

def maximum : Code := .call (ProgramLinking.liftProgram Max.program maxRegs maxStacks)

theorem maximum_eval (a : Data) (x y : ℕ)
    (hx : a.stacks 18 = unary x) (hy : a.stacks 15 = unary y) (ht : a.stacks 19 = []) :
    ∃ rf, Eval maximum (8*x+6) a
      ⟨rf,Function.update (Function.update a.stacks 18 []) 15 (unary (max x y))⟩ := by
  obtain ⟨rf,he⟩ := Max.command_eval (a.regs ∘ maxRegs) x y
  let b := Max.state rf [] (unary (max x y)) []
  have hp : projectState maxRegs maxStacks a = Max.state (a.regs ∘ maxRegs) (unary x) (unary y) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [maxStacks,hx,hy,ht]
  have tr := compiled_halt_trace he 0 1
  rw [← hp] at tr
  have hc := eval_call_from_state Max.program maxRegs maxStacks a maxRegs_injective maxStacks_injective tr
  let e := embedState maxRegs maxStacks a b
  have heq : e = ⟨e.regs,Function.update (Function.update a.stacks 18 []) 15 (unary (max x y))⟩ := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    by_cases h18 : i = 18
    · subst i; exact embedState_stack maxRegs maxStacks a b maxStacks_injective 0
    by_cases h15 : i = 15
    · subst i; exact embedState_stack maxRegs maxStacks a b maxStacks_injective 1
    by_cases h19 : i = 19
    · subst i
      calc
        Function.extend maxStacks b.stacks a.stacks 19 = b.stacks 2 := by
          simpa [maxStacks] using
            (maxStacks_injective.extend_apply b.stacks a.stacks 2)
        _ = Function.update (Function.update a.stacks 18 []) 15
            (unary (max x y)) 19 := by simp [b, ht]
    · have hf := embedState_stack_frame maxRegs maxStacks a b i (by
        rintro ⟨j,hj⟩; fin_cases j <;> simp [maxStacks] at hj <;> simp_all)
      change (embedState maxRegs maxStacks a b).stacks i =
        Function.update (Function.update a.stacks 18 []) 15 (unary (max x y)) i
      rw [Function.update_noteq h15, Function.update_noteq h18]
      exact hf
  refine ⟨e.regs,?_⟩
  change Eval maximum (8*x+5+1) a e at hc
  rw [heq] at hc
  convert hc using 1

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
