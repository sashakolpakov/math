import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOriginControl
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-!
# Source origins from the current Taylor cache in the node workspace

The native program reads the first shifted Taylor coefficient and reduces
its four words to source residues. This static placement preserves all
other cache and context ports. Its output227 is consumed by packet assembly.
-/

namespace SubexponentialSAT.SubexpNodeOriginStage

open BitProgram StructuredCalls

abbrev Data := State 16 288

def registers : Fin 14 → Fin 16 := Fin.castAdd 2
theorem registers_injective : Function.Injective registers := Fin.castAdd_injective _ _

def ports (i : Fin 32) : Fin 288 :=
  if i = 5 then 128 else if i = 10 then 74 else if i = 11 then 129
  else if i = 14 then 102 else if i = 24 then 227 else ⟨138 + i.val, by omega⟩

theorem ports_injective : Function.Injective ports := by decide

@[simp] theorem ports_modulus : ports 5 = 128 := by decide
@[simp] theorem ports_targetWidth : ports 10 = 74 := by decide
@[simp] theorem ports_sourceWidth : ports 11 = 129 := by decide
@[simp] theorem ports_cache : ports 14 = 102 := by decide
@[simp] theorem ports_output : ports 24 = 227 := by decide

def localState (d : Data) : SubexpOriginControl.Data := projectState registers ports d
def program := ProgramLinking.liftProgram SubexpOriginControl.program registers ports
abbrev command : Cmd 16 288 := .call program

/-- Lift an actual native run. The source-origin arithmetic and traversal
proof remains native; this theorem contributes only the fixed placement. -/
theorem command_eval_from_native (d : Data) (out : SubexpOriginControl.Data) (n : ℕ)
    (h : Trace SubexpOriginControl.program n
      ((localState d).withPC (some SubexpOriginControl.program.entry)) (out.withPC none)) :
    Eval command n d (embedState registers ports d out) :=
  eval_call_from_state SubexpOriginControl.program registers ports d
    registers_injective ports_injective h

theorem result_stacks (d : Data) (out : SubexpOriginControl.Data) (origins : List Bool)
    (h : out.stacks = Function.update (localState d).stacks 24 origins) :
    (embedState registers ports d out).stacks = Function.update d.stacks 227 origins := by
  change Function.extend ports out.stacks d.stacks = _
  rw [h, ProgramLinking.extend_update ports_injective]
  have hb := congrArg StructuredProgram.State.stacks
    (embedState_project registers ports d registers_injective ports_injective)
  change Function.extend ports (localState d).stacks d.stacks = d.stacks at hb
  rw [hb, ports_output]

theorem result_frame (d : Data) (out : SubexpOriginControl.Data) (origins : List Bool)
    (h : out.stacks = Function.update (localState d).stacks 24 origins)
    (i : Fin 288) (hi : i ≠ 227) :
    (embedState registers ports d out).stacks i = d.stacks i := by
  rw [result_stacks d out origins h]
  exact Function.update_of_ne hi _ _

end SubexponentialSAT.SubexpNodeOriginStage

end OAI.Algorithms
