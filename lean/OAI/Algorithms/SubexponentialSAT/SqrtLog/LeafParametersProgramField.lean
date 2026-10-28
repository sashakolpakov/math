import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramBounds
import OAI.Algorithms.SubexponentialSAT.SubexpBlockParameterProgram

namespace OAI.Algorithms

/-! A fixed binary power program produces the runtime field cardinality.
Its exponent word is data; no extension degree is compiled into the control. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Field

open BitProgram StructuredCalls BinaryArithmetic
open SubexpBlockParameterProgram

/-- Input exponent on port 1; output 3^d on port 2. Port 0 is private constant
space and is restored empty; all other input words are preserved. -/
abbrev command : Cmd 8 22 :=
  .seq (loadCmd 0 [true,true])
    (.seq (powerCmd 0 1 2 (by decide) (by decide))
      (ArithmeticExpressionSupport.clearCmd (port 0)))

def bound (exponent : List Bool) : ℕ :=
  PowerPrograms.runtimeBound [true,true] exponent + 9 * exponent.length + 19

theorem command_eval (regs : Regs) (words : Words)
    (h0 : words 0 = []) (h2 : words 2 = []) :
    ∃ t rf word, Eval command t (state regs words) (state rf (Function.update words 2 word)) ∧
      BinaryArithmetic.toNat word = 3 ^ BinaryArithmetic.toNat (words 1) ∧ word.length ≤ 1 + 2 * BinaryArithmetic.toNat (words 1) ∧
      t ≤ bound (words 1) := by
  obtain ⟨r0,hload⟩ := load_eval regs words 0 [true,true] h0
  let w0 := Function.update words 0 [true,true]
  obtain ⟨tp,rp,wp,hpower,hv,hl,ht⟩ := power_eval r0 w0 0 1 2
    (by decide) (by decide) (by simp [w0,h2])
  let w1 := Function.update w0 2 wp
  let a := state rp w1
  have hclear := ArithmeticExpressionSupport.clear_eval (port 0) a
  let rf := readRegs a.regs 0 1 none
  have hs : (⟨rf,Function.update a.stacks (port 0) []⟩ : Data) =
      state rf (Function.update words 2 wp) := by
    rw [show a = state rp w1 by rfl,state_update]
    congr 1
    funext i
    by_cases hi : i = 0
    · subst i; simp [w1,w0,h0]
    · by_cases hi2 : i = 2
      · subst i; simp [w1,w0]
      · simp [w1,w0,hi,hi2]
  have hc : Eval (ArithmeticExpressionSupport.clearCmd (port 0)) 7 a
      (state rf (Function.update words 2 wp)) := by
    change Eval _ (2*(a.stacks (port 0)).length+3) a
      (⟨rf,Function.update a.stacks (port 0) []⟩ : Data) at hclear
    rw [hs] at hclear
    have ha : a.stacks (port 0) = [true,true] := by simp [a,w1,w0]
    simpa [ha] using hclear
  refine ⟨4+(tp+7),rf,wp,hload.seq (hpower.seq hc),?_,?_,?_⟩
  · simpa [w0,BinaryArithmetic.toNat,bitVal] using hv
  · simpa [w0,Nat.mul_comm] using hl
  · simp [w0] at ht
    dsimp [bound]
    omega

theorem bound_polynomial (exponent : List Bool) :
    bound exponent ≤ 1000 * (BinaryArithmetic.toNat exponent + exponent.length + 2)^2 := by
  dsimp [bound,PowerPrograms.runtimeBound,PowerPrograms.workBound,PowerPrograms.callbackBound]
  nlinarith

abbrev program := compiled command 1 2

theorem program_runs (regs : Regs) (words : Words)
    (h0 : words 0 = []) (h2 : words 2 = []) :
    ∃ rf word, RunsIn program (bound (words 1)+1)
      ((state regs words).withPC (some program.entry))
      ((state rf (Function.update words 2 word)).withPC none) ∧
      BinaryArithmetic.toNat word = 3 ^ BinaryArithmetic.toNat (words 1) := by
  obtain ⟨t,rf,word,he,hv,hl,ht⟩ := command_eval regs words h0 h2
  exact ⟨rf,word,⟨t+1,by omega,compiled_halt_trace he 1 2⟩,hv⟩

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Field

end OAI.Algorithms
