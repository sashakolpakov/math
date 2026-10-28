import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSourceHost
import OAI.Algorithms.SubexponentialSAT.SubexpOuterJobs

namespace OAI.Algorithms

/-! The outer loop's concrete frame supplies the source constructor's
readiness condition when the current exponent word changes. -/

namespace SubexponentialSAT.SubexpSourceReady

open BitProgram StructuredCalls

abbrev Data := State 16 128
abbrev Context := SubexpMomentSourceProgram.Context

def initialStacks (ctx : Context) (r : Fin 8 → Bool) : Fin 63 → List Bool :=
  (SubexpMomentSourceProgram.state ctx r [] SubexpBlockAssembly.emptyBuffers [] [] [] []).stacks

theorem initialStacks_exponent (ctx : Context) (bits : List Bool) (r : Fin 8 → Bool) :
    initialStacks {ctx with exponent := bits} r =
      Function.update (initialStacks {ctx with exponent := []} r) 0 bits := by
  funext i
  fin_cases i <;> rfl

private theorem source_port_frame (i : Fin 63) :
    SubexpMomentSourceHost.ports i ≠ 14 ∧
      SubexpMomentSourceHost.ports i ≠ 110 ∧ SubexpMomentSourceHost.ports i ≠ 111 := by
  revert i
  decide

/-- All persistent source inputs and scratch stacks come from the existing
outer frame. Only X0 changes to the current actual word; source1 is empty. -/
theorem ready_of_frame (ctx : Context) (base d : Data) (bits : List Bool)
    (hbase : SubexpMomentSourceHost.Ready {ctx with exponent := []} base)
    (hframe : SubexpOuterJobs.Frame base d)
    (hbits : d.stacks 0 = bits) (hsource : d.stacks 1 = []) :
    SubexpMomentSourceHost.Ready {ctx with exponent := bits} d := by
  have hb (i : Fin 63) : base.stacks (SubexpMomentSourceHost.ports i) =
      initialStacks {ctx with exponent := []} (base.regs ∘ SubexpMomentSourceHost.registers) i :=
    congrFun (congrArg StructuredProgram.State.stacks hbase) i
  unfold SubexpMomentSourceHost.Ready
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    change d.stacks (SubexpMomentSourceHost.ports i) =
      initialStacks {ctx with exponent := bits} (d.regs ∘ SubexpMomentSourceHost.registers) i
    by_cases hi0 : i = 0
    · subst i
      simpa [SubexpMomentSourceHost.ports, initialStacks, SubexpMomentSourceProgram.state] using hbits
    by_cases hi1 : i = 1
    · subst i
      simpa [SubexpMomentSourceHost.ports, initialStacks, SubexpMomentSourceProgram.state] using hsource
    have hp0 : SubexpMomentSourceHost.ports i ≠ 0 := by
      intro h
      exact hi0 (SubexpMomentSourceHost.ports_injective
        (show SubexpMomentSourceHost.ports i = SubexpMomentSourceHost.ports 0 from h))
    have hp1 : SubexpMomentSourceHost.ports i ≠ 1 := by
      intro h
      exact hi1 (SubexpMomentSourceHost.ports_injective
        (show SubexpMomentSourceHost.ports i = SubexpMomentSourceHost.ports 1 from h))
    obtain ⟨hp14, hp110, hp111⟩ := source_port_frame i
    rw [initialStacks_exponent, Function.update_of_ne hi0]
    exact (hframe _ hp0 hp1 hp14 hp110 hp111).trans (hb i)

end SubexponentialSAT.SubexpSourceReady

end OAI.Algorithms
