import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLinearFactorProgram
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionStore
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Invoke the padded-linear constructor in the 256-stack polynomial
workspace, retaining a previously constructed zero coefficient on 104. -/

namespace SubexponentialSAT.SubexpLinearFactorCall

open BitProgram StructuredCalls SubexpConvolutionControl

def ports : Fin 128 ↪ Fin 256 := ⟨Fin.castAdd 128, Fin.castAdd_injective 128 128⟩

def command : Code :=
  liftCommand SubexpLinearFactorProgram.fromCounter 108 102 id ports

theorem command_run (s : Store) (D B : ℕ) (low high : List Bool)
    (hlow : s 100 = low) (hhigh : s 101 = high)
    (hllen : low.length = 4 * B) (hhlen : high.length = 4 * B)
    (hD : s 108 = List.replicate D true)
    (hzero : s 104 = List.replicate (4 * B) false)
    (hout : s 102 = []) (htmp : s 107 = []) :
    ExecutesIn command (101 * (D + 1) * (B + 1)) s
      (Function.update (Function.update s 108 []) 102
        (SubexpLinearFactorProgram.paddedBits B low high D)) := by
  intro regs
  let d : Data := ⟨regs, s⟩
  let nativeData := projectState id ports d
  obtain ⟨n, hn, rf, he⟩ := SubexpLinearFactorProgram.fromCounter_eval nativeData D B low high
    hlow hhigh hllen hhlen hD hzero hout htmp
  have hc := eval_liftCommand_from_state SubexpLinearFactorProgram.fromCounter
    108 102 id ports d Function.injective_id ports.injective he
  let last := embedState id ports d
    (SubexpLinearFactorProgram.counterResult nativeData D B low high rf)
  have hext : Function.extend ports (s ∘ ports) s = s := by
    have h := congrArg StructuredProgram.State.stacks
      (embedState_project id ports d Function.injective_id ports.injective)
    exact h
  have hs : last.stacks = Function.update (Function.update s 108 []) 102
      (SubexpLinearFactorProgram.paddedBits B low high D) := by
    change Function.extend ports
      (Function.update (Function.update (s ∘ ports) 108 []) 102
        (SubexpLinearFactorProgram.paddedBits B low high D)) s = _
    rw [ProgramLinking.extend_update ports.injective,
      ProgramLinking.extend_update ports.injective, hext]
    rfl
  have hlast : last =
      (⟨last.regs, Function.update (Function.update s 108 []) 102
        (SubexpLinearFactorProgram.paddedBits B low high D)⟩ : Data) := by
    exact SubexpScanPrimitives.state_ext rfl hs
  refine ⟨n + 1, last.regs, ?_, ?_⟩
  · have hp : 0 < (D + 1) * (B + 1) := Nat.mul_pos (by omega) (by omega)
    nlinarith
  · change Eval command (n + 1) d last at hc
    rw [hlast] at hc
    exact hc

end SubexponentialSAT.SubexpLinearFactorCall

end OAI.Algorithms
