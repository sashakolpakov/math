import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-! Extensional frame rules for connecting finite programs on fixed ports. -/

namespace SubexponentialSAT.ProgramLinking

open BitProgram

/-- Identify an embedded configuration by its assigned ports and its frame.
This is a proof rule; the executable table uses the finite port maps directly. -/
theorem embedCfg_eq_of_ports {r s l R S L : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L))
    (frame target : Cfg R S L) (source : Cfg r s l)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (hpc : relocatePc label returnPc source.pc = target.pc)
    (hreg : ∀ i, target.regs (register i) = source.regs i)
    (hregFrame : ∀ i, (¬ ∃ j, register j = i) → target.regs i = frame.regs i)
    (hstack : ∀ i, target.stacks (stack i) = source.stacks i)
    (hstackFrame : ∀ i, (¬ ∃ j, stack j = i) → target.stacks i = frame.stacks i) :
    embedCfg register stack label returnPc frame source = target := by
  have hregs : (embedCfg register stack label returnPc frame source).regs = target.regs := by
    funext i
    classical
    by_cases hi : ∃ j, register j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (embedCfg_register register stack label returnPc frame source hr j).trans
        (hreg j).symm
    · exact (embedCfg_register_frame register stack label returnPc frame source i hi).trans
        (hregFrame i hi).symm
  have hstacks : (embedCfg register stack label returnPc frame source).stacks = target.stacks := by
    funext i
    classical
    by_cases hi : ∃ j, stack j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (embedCfg_stack register stack label returnPc frame source hs j).trans
        (hstack j).symm
    · exact (embedCfg_stack_frame register stack label returnPc frame source i hi).trans
        (hstackFrame i hi).symm
  cases target
  cases he : embedCfg register stack label returnPc frame source
  simp_all [embedCfg]

end SubexponentialSAT.ProgramLinking

namespace SubexponentialSAT.StructuredCalls

/-- The corresponding data-only frame rule for structured subroutine calls. -/
theorem embedState_eq_of_ports {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame target : State R S) (source : State r s)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (hreg : ∀ i, target.regs (register i) = source.regs i)
    (hregFrame : ∀ i, (¬ ∃ j, register j = i) → target.regs i = frame.regs i)
    (hstack : ∀ i, target.stacks (stack i) = source.stacks i)
    (hstackFrame : ∀ i, (¬ ∃ j, stack j = i) → target.stacks i = frame.stacks i) :
    embedState register stack frame source = target := by
  have h := ProgramLinking.embedCfg_eq_of_ports register stack (id : Fin 1 → Fin 1) none
    (frame.withPC none) (target.withPC none) (source.withPC none) hr hs rfl
    hreg hregFrame hstack hstackFrame
  exact congrArg StructuredProgram.State.ofCfg h

end SubexponentialSAT.StructuredCalls

end OAI.Algorithms
