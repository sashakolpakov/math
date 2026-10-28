import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgramInstall

namespace OAI.Algorithms

/-! Raw scope bytes and a mask produce the actual installed incidence-pair table. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
abbrev Data := State 16 48

def ports (i : Fin 32) : Fin 48 :=
  if i=20 then 32 else if i=21 then 33 else if i=22 then 34
  else if i=24 then 35 else if i=25 then 20 else if i=26 then 36 else i.castAdd 16
theorem ports_injective : Function.Injective ports := by decide
def frame (r : Fin 16 → Bool) : Data := ⟨r,fun _ => []⟩
noncomputable def state (d : Scan.Data) : Data := embedState id ports (frame d.regs) d
noncomputable def input (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :=
  state (Scan.data r scopes n 0 0 mask [])
noncomputable def produced (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :=
  state (Scan.data r scopes n mask.length (Loop.finalCounter scopes 0 scopes.length mask) []
    (ProgramEncoding.encodeRecords (PackingIncidenceProgram.planAlphabet
      (Loop.plans scopes n 0 scopes.length mask))))
abbrev build : Cmd 16 48 := .call (ProgramLinking.liftProgram Boot.fullProgram id ports)
abbrev depth : Cmd 16 48 := .seq (TupleProgram.pushConst 27 0 true) (TupleProgram.pushConst 27 0 true)
def withDepth (d : Data) := TupleProgram.pushedState 27 0 true
  (TupleProgram.pushedState 27 0 true d)
abbrev command : Cmd 16 48 := .seq build (.seq depth PackingIncidenceProgram.Install.command)
def program := compiled command 32 45
def plans (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :=
  Loop.plans scopes n 0 scopes.length mask
def budget (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :=
  Boot.fullBudget scopes n mask + 4 + PackingIncidenceProgram.Install.budget (plans scopes n mask)

theorem state_register (d : Scan.Data) (i : Fin 16) : (state d).regs i = d.regs i :=
  embedState_register id ports (frame d.regs) d Function.injective_id i
theorem state_stack (d : Scan.Data) (i : Fin 32) : (state d).stacks (ports i) = d.stacks i :=
  embedState_stack id ports (frame d.regs) d ports_injective i
theorem state_frame (d : Scan.Data) (j : Fin 48) (hj : ¬ ∃ i, ports i=j) :
    (state d).stacks j = [] :=
  embedState_stack_frame id ports (frame d.regs) d j hj

theorem build_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    ∃ t rf, t ≤ Boot.fullBudget scopes n mask ∧
      Eval build t (input r scopes n mask) (produced rf scopes n mask) := by
  obtain ⟨t,rf,ht,he⟩ := Boot.full_eval r scopes n mask
  have h := eval_call_lifted Boot.fullProgram id ports (frame r)
    Function.injective_id ports_injective (compiled_halt_trace he 20 25)
  have hframe (d : Scan.Data) : embedState id ports (frame r) d = state d := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      have h1 := embedState_register id ports (frame r) d Function.injective_id i
      have h2 := state_register d i
      exact h1.trans h2.symm
    · rfl
  exact ⟨t+1,rf,ht,by simpa [build, input, produced, hframe] using h⟩

theorem depth_eval (d : Data) : Eval depth 4 d (withDepth d) :=
  (TupleProgram.pushConst_eval (27 : Fin 48) (0 : Fin 16) true d).seq
    (TupleProgram.pushConst_eval (27 : Fin 48) (0 : Fin 16) true
      (TupleProgram.pushedState 27 0 true d))

theorem installed_input (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    PackingIncidenceProgram.Install.Input (plans scopes n mask)
      (withDepth (produced r scopes n mask)) := by
  let d := Scan.data r scopes n mask.length (Loop.finalCounter scopes 0 scopes.length mask) []
    (ProgramEncoding.encodeRecords (PackingIncidenceProgram.planAlphabet (plans scopes n mask)))
  have hs (j : Fin 32) : (produced r scopes n mask).stacks (ports j) = d.stacks j :=
    state_stack d j
  have h21 : (produced r scopes n mask).stacks 21 = [] := state_frame d 21 (by decide)
  have h22 : (produced r scopes n mask).stacks 22 = [] := state_frame d 22 (by decide)
  have h24 : (produced r scopes n mask).stacks 24 = [] := state_frame d 24 (by decide)
  have h25 : (produced r scopes n mask).stacks 25 = [] := state_frame d 25 (by decide)
  have h26 : (produced r scopes n mask).stacks 26 = [] := state_frame d 26 (by decide)
  have h45 : (produced r scopes n mask).stacks 45 = [] := state_frame d 45 (by decide)
  have h0 := hs 0
  have h7 := hs 7
  have h20 := hs 25
  have h23 := hs 23
  have h27 := hs 27
  simp [ports] at h0 h7 h20 h23 h27
  constructor
  · intro i
    fin_cases i <;> simp [PackingIncidenceProgram.Install.ports,withDepth,
      TupleProgram.pushedState,PackingIncidenceProgram.pairInput,
      h0,h20,h21,h22,h23,h24,h25,h26,h27,d,Scan.data]
  · constructor <;> simp [withDepth,TupleProgram.pushedState,h7,h45,d,Scan.data]

/-- The only combinatorial input is the serialized scope stream and mask.
The linear addresses, all ordered pairs, and their installation are paid. -/
theorem command_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    ∃ t e, t+1 ≤ budget scopes n mask ∧
      Eval command t (input r scopes n mask) e ∧
      e.stacks 45 = PairScoreProgram.pairRecords
        (PackingIncidenceProgram.generatedRawPairs (plans scopes n mask)) := by
  obtain ⟨tb,rb,htb,hb⟩ := build_eval r scopes n mask
  obtain ⟨ti,hti,e,he,hout,_,_⟩ := PackingIncidenceProgram.Install.command_eval
    (plans scopes n mask) (withDepth (produced rb scopes n mask))
    (installed_input rb scopes n mask)
  refine ⟨tb+(4+ti),e,?_,hb.seq ((depth_eval _).seq he),hout⟩
  dsimp [budget]; omega

theorem primitive_run (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    ∃ e : Data, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * budget scopes n mask)
      (primitiveCfg program ((input r scopes n mask).withPC (some program.entry)))
      (primitiveCfg program (e.withPC none)) ∧
      e.stacks 45 = PairScoreProgram.pairRecords
        (PackingIncidenceProgram.generatedRawPairs (plans scopes n mask)) := by
  obtain ⟨t,e,ht,he,hout⟩ := command_eval r scopes n mask
  exact ⟨e,BitProgram.primitive_execution program ⟨t+1,ht,compiled_halt_trace he 32 45⟩,hout⟩
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install

end OAI.Algorithms
