import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrapPreparation
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchNativeScan

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open BitProgram StructuredCalls
open SubexpEnumerationPayload SubexpTupleRefinement IrreducibleSearchProgram
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

theorem tableWord_factor (d : ℕ) : tableWord ((d + 1) + (d + 1)) =
    ProgramEncoding.encodeRecords (IrreducibleSearchFactorControl.factorRecords d) := by
  unfold tableWord
  rw [IrreducibleSearch.encoded_factorPairs]
  unfold IrreducibleSearchFactorControl.factorRecords
  apply congrArg ProgramEncoding.encodeRecords
  apply List.map_congr_left
  intro ab _
  simp only [IrreducibleSearchFactorControl.pairEncode,
    coefficientArray_append, coefficientArray_ofFn]

theorem finalState_eq (depth : List Bool) :
    state depth (false :: depth) (tableWord depth.length)
      (tableWord ((depth.length + 1) + (depth.length + 1))) [] [] (fun _ => false) =
    IrreducibleSearchCandidateControl.input depth.length depth (false :: depth) [] := by
  rw [tableWord_factor]
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    fin_cases i <;> simp [
 IrreducibleSearchCandidateControl.readyLow,
      IrreducibleSearchFactorControl.wide, pairState]
  · funext i
    fin_cases i <;> simp [layout,

      IrreducibleSearchCandidateControl.readyLow, IrreducibleSearchFactorControl.wide,
      pairState, tableWord, IrreducibleSearchCandidateControl.candidateRecords]

/-- The actual machine input has only its unary depth stack populated. -/
def input (depth : List Bool) : Data := StructuredProgram.ioState 14 depth

theorem input_eq (depth : List Bool) : input depth =
    state depth [] [] [] [] [] (fun _ => false) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;> simp [ layout]

theorem bootstrap_eval (depth : List Bool) :
    ∃ t, t ≤ cost depth.length ∧ Eval command t (input depth)
      (IrreducibleSearchCandidateControl.input depth.length depth (false :: depth) []) := by
  simpa only [← input_eq, finalState_eq] using command_eval depth (fun _ => false)

def program := compiled command 14 24

theorem program_runsIn (depth : List Bool) :
    RunsIn program (cost depth.length + 1)
      ((input depth).withPC (some program.entry))
      ((IrreducibleSearchCandidateControl.input depth.length depth (false :: depth) []).withPC none) := by
  obtain ⟨t, ht, he⟩ := bootstrap_eval depth
  exact ⟨t + 1, Nat.add_le_add_right ht 1, compiled_halt_trace he 14 24⟩

theorem program_primitive (depth : List Bool) :
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (cost depth.length + 1))
      (primitiveCfg program ((input depth).withPC (some program.entry)))
      (primitiveCfg program
        ((IrreducibleSearchCandidateControl.input depth.length depth (false :: depth) []).withPC none)) :=
  BitProgram.primitive_execution program (program_runsIn depth)

/-- All table preparation and the first-success scan share one fixed program. -/
abbrev searchCommand : Cmd 22 28 :=
  .seq command (.call IrreducibleSearchCandidateControl.program)

def searchProgram := compiled searchCommand 14 13

def totalCost (d : ℕ) : ℕ := cost d + IrreducibleSearchCandidateControl.searchCost d + 1

theorem searchCommand_eval (depth : List Bool) (hd : 0 < depth.length) :
    ∃ (t : ℕ) (final : Data), t + 1 ≤ totalCost depth.length ∧
      final.stacks 13 = encodeTuple (scalarCode 3) (IrreducibleSearch.coefficients depth.length) ∧
      IrreducibleSearchCandidateControl.Ready depth.length depth (false :: depth) [] final ∧
      final.stacks 25 = [] ∧ Eval searchCommand t (input depth) final := by
  obtain ⟨t, ht, he⟩ := bootstrap_eval depth
  obtain ⟨final, hout, hready, h25, u, hu, hr⟩ :=
    IrreducibleSearchCandidateControl.program_runsIn_ready hd depth (false :: depth) [] rfl rfl
  refine ⟨t + u, final, ?_, hout, hready, h25,
    he.seq (.call IrreducibleSearchCandidateControl.program hr)⟩
  dsimp only [totalCost]
  omega

theorem searchProgram_runsIn (depth : List Bool) (hd : 0 < depth.length) :
    ∃ final : Data, final.stacks 13 =
        encodeTuple (scalarCode 3) (IrreducibleSearch.coefficients depth.length) ∧
      IrreducibleSearchCandidateControl.Ready depth.length depth (false :: depth) [] final ∧
      final.stacks 25 = [] ∧ RunsIn searchProgram (totalCost depth.length)
        ((input depth).withPC (some searchProgram.entry)) (final.withPC none) := by
  obtain ⟨t, final, ht, hout, hready, h25, he⟩ := searchCommand_eval depth hd
  exact ⟨final, hout, hready, h25, t + 1, ht, compiled_halt_trace he 14 13⟩

theorem searchProgram_primitive (depth : List Bool) (hd : 0 < depth.length) :
    ∃ final : Data, final.stacks 13 =
        encodeTuple (scalarCode 3) (IrreducibleSearch.coefficients depth.length) ∧
      IrreducibleSearchCandidateControl.Ready depth.length depth (false :: depth) [] final ∧
      final.stacks 25 = [] ∧
      Computation.RunsIn (primitive searchProgram).step
        (primitiveOverhead searchProgram * totalCost depth.length)
        (primitiveCfg searchProgram ((input depth).withPC (some searchProgram.entry)))
        (primitiveCfg searchProgram (final.withPC none)) := by
  obtain ⟨final, hout, hready, h25, hr⟩ := searchProgram_runsIn depth hd
  exact ⟨final, hout, hready, h25, BitProgram.primitive_execution searchProgram hr⟩


end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

end OAI.Algorithms
