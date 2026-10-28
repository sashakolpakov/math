import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramBase
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramLocalProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramGraphProgram

namespace OAI.Algorithms

/-! Fixed local-code and Walsh graph search stages, with physical routing. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls

def localInputs : List Route := [(809,19),(811,20),(808,28),(810,29)]
def localOutputs : List Route := [(18,815)]
abbrev localCode : Cmd 40 896 :=
  stage localInputs CodeSearchProgram.localProgram regs20 stacks32 localOutputs

def graphInputs : List Route := [(808,30),(800,31),(801,32),(812,40),(813,41)]
def graphOutputs : List Route := [(29,816)]
abbrev graphCode : Cmd 40 896 :=
  stage graphInputs CodeSearchProgram.graphProgram regs20 stacks44 graphOutputs


theorem localInputs_valid : ∀ p ∈ localInputs, routeValid p := by
  intro p hp
  simp only [localInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl
  all_goals unfold routeValid; decide
theorem localOutputs_valid : ∀ p ∈ localOutputs, routeValid p := by
  intro p hp
  simp only [localOutputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl
  all_goals unfold routeValid; decide
theorem graphInputs_valid : ∀ p ∈ graphInputs, routeValid p := by
  intro p hp
  simp only [graphInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl
  all_goals unfold routeValid; decide
theorem graphOutputs_valid : ∀ p ∈ graphOutputs, routeValid p := by
  intro p hp
  simp only [graphOutputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl
  all_goals unfold routeValid; decide

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
