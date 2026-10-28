import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramBasic

namespace OAI.Algorithms

/-! Preserve the physically generated owner/factor plans before the incidence
pair installer consumes them. The extra master is local port61. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open PackingLoaderProgram PackingIncidenceInput

def planBits (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :=
  ProgramEncoding.encodeRecords (PackingIncidenceProgram.planAlphabet (Install.plans scopes n mask))

def buildProgram := compiled Install.build 32 20

abbrev incidenceTail : Cmd 16 48 := .seq Install.depth PackingIncidenceProgram.Install.command
def incidenceTailProgram := compiled incidenceTail 20 45

theorem produced_regs (regs : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    (Install.produced regs scopes n mask).regs=regs := by
  funext i
  exact Install.state_register _ i

theorem produced_setRegs (regs rs : Fin 16 → Bool) (scopes : List (List ℕ))
    (n : ℕ) (mask : List Bool) :
    setRegs (Install.produced regs scopes n mask) rs=Install.produced rs scopes n mask := by
  apply SubexponentialSAT.CounterForPrograms.data_ext
  · exact (produced_regs rs scopes n mask).symm
  · change (Install.produced regs scopes n mask).stacks=(Install.produced rs scopes n mask).stacks
    rw [Endpoint.produced_stacks,Endpoint.produced_stacks]

theorem incidenceTail_eval (regs : Fin 16 → Bool) (scopes : List (List ℕ))
    (n : ℕ) (mask : List Bool) :
    ∃ t rf, t+1 ≤ 4+PackingIncidenceProgram.Install.budget (Install.plans scopes n mask) ∧
      Eval incidenceTail t (Install.produced regs scopes n mask) (Endpoint.result rf scopes n mask) := by
  obtain ⟨ti,hti,e,he,hout,hz,hf⟩ := PackingIncidenceProgram.Install.command_eval
    (Install.plans scopes n mask) (Install.withDepth (Install.produced regs scopes n mask))
    (Install.installed_input regs scopes n mask)
  have hend := Endpoint.exact_output regs scopes n mask e hout hz hf
  have hrun := (Install.depth_eval (Install.produced regs scopes n mask)).seq he
  rw [hend] at hrun
  exact ⟨4+ti,e.regs,by omega,hrun⟩

def produce : Code := .seq (.call (ProgramLinking.liftProgram buildProgram id lowPorts))
  (.seq (saveHigh 20 61) (.call (ProgramLinking.liftProgram incidenceTailProgram id lowPorts)))

def produceBudget (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :=
  Boot.fullBudget scopes n mask+1 + (7*(planBits scopes n mask).length+5) +
    (4+PackingIncidenceProgram.Install.budget (Install.plans scopes n mask))

theorem produce_eval (outside : Store) (regs : Fin 16 → Bool)
    (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (h52 : outside 52=[]) (h61 : outside 61=[]) :
    ∃ t rf, t ≤ produceBudget scopes n mask ∧ Eval produce t
      (framed outside (Install.input regs scopes n mask))
      (framed (Function.update outside 61 (planBits scopes n mask))
        (Endpoint.result rf scopes n mask)) := by
  obtain ⟨tb,rb,htb,hb⟩ := Install.build_eval regs scopes n mask
  have hbuild := framed_call buildProgram outside (compiled_halt_trace hb 32 20)
  obtain ⟨rs,hs⟩ := saveHigh_eval outside (Install.produced rb scopes n mask) 20 61
    (by decide) (by decide) h52 h61
  have hplans : (Install.produced rb scopes n mask).stacks 20=planBits scopes n mask := by
    rw [Endpoint.produced_stacks]
    simp [Endpoint.builtStacks,planBits]
  rw [hplans,produced_setRegs] at hs
  obtain ⟨tt,rf,htt,ht⟩ := incidenceTail_eval rs scopes n mask
  have htail := framed_call incidenceTailProgram
    (Function.update outside 61 (planBits scopes n mask)) (compiled_halt_trace ht 20 45)
  exact ⟨tb+1+((7*(planBits scopes n mask).length+5)+(tt+1)),rf,
    by dsimp [produceBudget]; omega,hbuild.seq (hs.seq htail)⟩

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
