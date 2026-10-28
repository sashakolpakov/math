import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceBank

namespace OAI.Algorithms

/-! Measured native stages used by the packed source dispatcher. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

theorem lowRegs_inj : Function.Injective lowRegs := Fin.castAdd_injective _ _
theorem mismatchPorts_inj : Function.Injective mismatchPorts := by decide
theorem emitterRegs_inj : Function.Injective emitterRegs := Fin.castAdd_injective _ _
theorem emitterPorts_inj : Function.Injective emitterPorts := by
  intro i j h
  apply Fin.ext
  have hh := congrArg Fin.val h
  simp only [emitterPorts] at hh
  omega

theorem mismatches_eval {r Q : ℕ} (u y : UniversalType r Q 1) (a : Data)
    (ha : UniversalRowMismatchTypes.InputReady (0 : Fin 1) u y
      (projectState lowRegs mismatchPorts a)) (he : a.stacks 71=[]) :
    ∃ n ≤ UniversalRowMismatchTypes.extractBudget (r:=r) (Q:=Q) (0:Fin 1)+
      UniversalRowMismatchProgram.budget Q r+8*(Q*r)+13,
      ∃ b : Data, Eval mismatches n a b ∧
        b.stacks=Function.update a.stacks 71
          (ProgramEncoding.encodeRecords (MismatchPlanProgram.indexRecords
            (MismatchPlanProgram.selectedPositions y.head (u.slot 0)).reverse)) := by
  let small := projectState lowRegs mismatchPorts a
  obtain ⟨n,hn,z,hz,hzs⟩ := UniversalRowMismatchTypes.command_eval (0:Fin 1) u y small ha
    (by simpa [small,projectState,mismatchPorts] using he)
  let b := embedState lowRegs mismatchPorts a z
  have hh := eval_liftCommand_from_state UniversalRowMismatchTypes.command 23 45 lowRegs
    mismatchPorts a lowRegs_inj mismatchPorts_inj hz
  refine ⟨n+1,by omega,b,hh,?_⟩
  change Function.extend mismatchPorts z.stacks a.stacks=_
  rw [hzs,ProgramLinking.extend_update mismatchPorts_inj]
  have hb := congrArg StructuredProgram.State.stacks
    (embedState_project lowRegs mismatchPorts a lowRegs_inj mismatchPorts_inj)
  change Function.extend mismatchPorts small.stacks a.stacks=a.stacks at hb
  rw [hb]
  rfl

theorem emit_eval (tables : UniversalRowLoop.Tables) (width rowWidth : List Bool)
    (positions : List ℕ) (valid : UniversalRowLoop.Valid tables width rowWidth positions)
    (delta limit zero one : List Bool) (a : Data)
    (ha : UniversalRowLoop.ready tables width rowWidth positions
      (projectState emitterRegs emitterPorts a))
    (hd : a.stacks 274=delta) (hl : a.stacks 269=limit)
    (hz : a.stacks 259=zero) (ho : a.stacks 266=one)
    (h14 : a.stacks 270=[]) (h17 : a.stacks 273=[]) (h31 : a.stacks 287=[]) :
    ∃ n ≤ UniversalRowSourceProgram.bound tables width rowWidth positions delta limit zero one,
      ∃ b : Data, Eval emit n a b ∧
        b.stacks=Function.update (Function.update a.stacks 274 []) 287
          (UniversalRowProgram.rowCode zero one (zero++one)
            (UniversalRowDataProgram.row tables positions delta limit)) := by
  let small := projectState emitterRegs emitterPorts a
  obtain ⟨z,⟨n,hn,he⟩,hstack⟩ := UniversalRowSourceProgram.program_runsIn tables width rowWidth
    positions valid delta limit zero one small ha hd hl hz ho h14 h17 h31
  let b := embedState emitterRegs emitterPorts a z
  have hh := eval_call_from_state UniversalRowSourceProgram.program emitterRegs emitterPorts a
    emitterRegs_inj emitterPorts_inj he
  refine ⟨n,hn,b,hh,?_⟩
  change Function.extend emitterPorts z.stacks a.stacks=_
  rw [hstack,ProgramLinking.extend_update emitterPorts_inj,ProgramLinking.extend_update emitterPorts_inj]
  have hb := congrArg StructuredProgram.State.stacks
    (embedState_project emitterRegs emitterPorts a emitterRegs_inj emitterPorts_inj)
  change Function.extend emitterPorts small.stacks a.stacks=a.stacks at hb
  rw [hb]
  rfl

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
