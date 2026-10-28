import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import Mathlib.Data.Fin.Basic

/-! Fixed disjoint register and stack banks for the counting machine. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI

def dfsRegisters : Fin 32 ↪ Fin 80 := Fin.castAddEmb 48

def dfsStacks : Fin 320 ↪ Fin 1220 := Fin.castAddEmb 900

def leafRegisters : Fin 40 ↪ Fin 80 :=
  (Fin.natAddEmb 32).trans (Fin.castAddEmb 8)

def leafStacks : Fin 896 ↪ Fin 1220 :=
  (Fin.natAddEmb 320).trans (Fin.castAddEmb 4)

def positivityRegisters : Fin 3 ↪ Fin 80 :=
  (Fin.natAddEmb 72).trans (Fin.castAddEmb 5)

def countStack : Fin 1220 := 256

def answerStack : Fin 1220 := 1216

def positivityScratch : Fin 1220 := 1217

theorem countStack_ne_answerStack : countStack ≠ answerStack := by decide

theorem dfs_leaf_registers_disjoint (i : Fin 32) (j : Fin 40) :
    dfsRegisters i ≠ leafRegisters j := by
  intro h
  have := congrArg Fin.val h
  change i.val = 32 + j.val at this
  omega

theorem dfs_leaf_stacks_disjoint (i : Fin 320) (j : Fin 896) :
    dfsStacks i ≠ leafStacks j := by
  intro h
  have := congrArg Fin.val h
  change i.val = 320 + j.val at this
  omega

theorem leaf_answer_disjoint (i : Fin 896) : leafStacks i ≠ answerStack := by
  intro h
  have := congrArg Fin.val h
  change 320 + i.val = 1216 at this
  omega

theorem leaf_count_disjoint (i : Fin 896) : leafStacks i ≠ countStack := by
  intro h
  have := congrArg Fin.val h
  change 320 + i.val = 256 at this
  omega

/-- A real finite leaf table is installed in the disjoint upper bank. -/
def leafCall {l : ℕ} (p : BitProgram.Program 40 896 l) : StructuredCalls.Cmd 80 1220 :=
  .call (ProgramLinking.liftProgram p leafRegisters leafStacks)

theorem leafCall_eval {l steps : ℕ} (p : BitProgram.Program 40 896 l)
    (frame : StructuredCalls.State 80 1220) {a b : StructuredCalls.State 40 896}
    (h : BitProgram.Trace p steps (a.withPC (some p.entry)) (b.withPC none)) :
    StructuredCalls.Eval (leafCall p) steps
      (StructuredCalls.embedState leafRegisters leafStacks frame a)
      (StructuredCalls.embedState leafRegisters leafStacks frame b) :=
  StructuredCalls.eval_call_lifted p leafRegisters leafStacks frame
    leafRegisters.injective leafStacks.injective h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI
