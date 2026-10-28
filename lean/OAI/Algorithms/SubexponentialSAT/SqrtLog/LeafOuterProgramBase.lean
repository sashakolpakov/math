import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramStorage
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgramUnary

namespace OAI.Algorithms

/-! Shared fixed port maps and the paid native code-parameter stage. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls

def regs8 : Fin 8 → Fin 40 := Fin.castAdd 32
def regs16 : Fin 16 → Fin 40 := Fin.castAdd 24
def regs20 : Fin 20 → Fin 40 := Fin.castAdd 20
def stacks77 : Fin 77 → Fin 896 := Fin.castAdd 819
def stacks32 : Fin 32 → Fin 896 := Fin.castAdd 864
def stacks44 : Fin 44 → Fin 896 := Fin.castAdd 852
def stacks64 : Fin 64 → Fin 896 := Fin.castAdd 832

def parameterInputs : List Route := [(782,0),(786,1)]
def parameterOutputs : List Route :=
  [(5,800),(9,801),(11,802),(12,803),(15,804),(18,805),(19,806),(21,807),
   (24,808),(25,809),(26,810),(27,811),(28,812),(29,813),(30,814)]
abbrev parameters : Cmd 40 896 :=
  stage parameterInputs CodeParametersProgram.program regs8 stacks77 parameterOutputs


theorem parameterInputs_valid : ∀ p ∈ parameterInputs, routeValid p := by
  intro p hp
  simp only [parameterInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl
  all_goals unfold routeValid; decide
theorem parameterOutputs_valid : ∀ p ∈ parameterOutputs, routeValid p := by
  intro p hp
  simp only [parameterOutputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals unfold routeValid; decide

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
