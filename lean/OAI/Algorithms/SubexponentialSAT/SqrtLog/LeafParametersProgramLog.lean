import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SetupPrimitives

namespace OAI.Algorithms

/-! The extension-degree operation is a fixed instruction table, working on
arbitrary padded binary input. The zero case is guarded separately. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram

open BitProgram StructuredCalls
open CounterPrograms (value ripple)

abbrev LogData := StructuredProgram.State 3 3

abbrev resetLog : Cmd 3 3 := .base (SubexpParameterProgram.atoms
  [.set 0 false, .set 1 false, .set 2 false])

abbrev logSizeSuccCommand : Cmd 3 3 :=
  .seq resetLog (.seq Setup.logSucc Setup.increment)

theorem resetLog_eval (d : LogData) :
    Eval resetLog 3 d ⟨fun _ => false, d.stacks⟩ := by
  have h := SubexpParameterProgram.atoms_eval
    ([.set 0 false, .set 1 false, .set 2 false] : List (StructuredProgram.Atom 3 3)) d
  have he : SubexpParameterProgram.runAtoms
      [.set 0 false, .set 1 false, .set 2 false] d = ⟨fun _ => false, d.stacks⟩ := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · rfl
  exact .base (he ▸ h)

theorem logSizeSuccCommand_eval (xs : List Bool) (d : LogData)
    (hs : d.stacks = (Setup.io xs).stacks) :
    ∃ output t, value output = Nat.log2 (value xs) + 2 ∧
      output.length ≤ xs.length + 2 ∧ t ≤ 64 * (xs.length + 2)^2 ∧
      Eval logSizeSuccCommand t d (Setup.io output) := by
  obtain ⟨ys,t,hv,hl,ht,he⟩ := Setup.logSucc_eval xs
  have hr : Eval resetLog 3 d (Setup.io xs) := by
    simpa only [hs] using resetLog_eval d
  refine ⟨ripple true ys,3+(t+(CounterPrograms.rippleCost true ys+1)),?_,?_,?_,
    hr.seq (he.seq (Setup.increment_eval ys))⟩
  · rw [CounterPrograms.value_increment,hv]
  · exact (CounterPrograms.ripple_length_le true ys).trans (by omega)
  · have hc := CounterPrograms.rippleCost_le true ys
    nlinarith

abbrev logSizeSuccProgram := compiled logSizeSuccCommand 0 0

theorem extensionDegree_program (xs : List Bool) (hx : value xs ≠ 0) :
    ∃ output, value output = extensionDegree (value xs) ∧
      output.length ≤ xs.length + 2 ∧
      RunsIn logSizeSuccProgram (65 * (xs.length + 2)^2)
        (initial logSizeSuccProgram xs) (terminal logSizeSuccProgram output) := by
  obtain ⟨output,t,hv,hl,ht,he⟩ := logSizeSuccCommand_eval xs (Setup.io xs) rfl
  refine ⟨output,?_,hl,t+1,by nlinarith,compiled_io_trace 0 0 he⟩
  simpa [extensionDegree,size_eq_log2_add_one hx,Nat.add_assoc] using hv

theorem extensionDegree_primitive (xs : List Bool) (hx : value xs ≠ 0) :
    ∃ output, value output = extensionDegree (value xs) ∧
      Computation.RunsIn (primitive logSizeSuccProgram).step
        (primitiveOverhead logSizeSuccProgram * (65 * (xs.length + 2)^2))
        (primitiveCfg logSizeSuccProgram (initial logSizeSuccProgram xs))
        (primitiveCfg logSizeSuccProgram (terminal logSizeSuccProgram output)) := by
  obtain ⟨output,hv,hl,hr⟩ := extensionDegree_program xs hx
  exact ⟨output,hv,primitive_execution logSizeSuccProgram hr⟩

end SubexponentialSAT.SqrtLog.LeafParametersProgram

end OAI.Algorithms
