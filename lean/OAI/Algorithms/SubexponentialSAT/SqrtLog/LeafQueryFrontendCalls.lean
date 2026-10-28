import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendOps
import OAI.Algorithms.SubexponentialSAT.SqrtLog.EarlyThreshold
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramPrepareBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramMask
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgramAudit
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgramRun

namespace OAI.Algorithms

/-! The frontend calls only concrete finite machines. All state embeddings
below are specifications of actual calls, never free data transformations. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

abbrev r2 := registers 2 (by decide)
abbrev r3 := registers 3 (by decide)
abbrev r8 := registers 8 (by decide)
abbrev r9 := registers 9 (by decide)
abbrev r10 := registers 10 (by decide)
abbrev r11 := registers 11 (by decide)

theorem call_run {r s l : ℕ} (p : Program r s l) (rr : Fin r → Fin 40)
    (ss : Fin s → Fin 768) (hr : Function.Injective rr) (hs : Function.Injective ss)
    (a : Data) (b : State r s) (B : ℕ)
    (h : RunsIn p B ((projectState rr ss a).withPC (some p.entry)) (b.withPC none)) :
    ∃ n ≤ B, Eval (.call (ProgramLinking.liftProgram p rr ss)) n a (embedState rr ss a b) := by
  obtain ⟨n,hn,ht⟩ := h
  exact ⟨n,hn,eval_call_from_state p rr ss a hr hs ht⟩

def earlyCall : Code := .call (ProgramLinking.liftProgram EarlyThreshold.program r8 early)
def highCall : Code := .call (ProgramLinking.liftProgram HighIncidenceProgram.Prepare.program r10 high)
def maskCall : Code := .call (ProgramLinking.liftProgram HighIncidenceProgram.Mask.program r2 mask)
def statsCall : Code := .call (ProgramLinking.liftProgram LeafStatisticsProgram.program r10 stats)
def arityCall : Code := .call (ProgramLinking.liftProgram LeafStatisticsProgram.Arity.program r10 arity)
def finishCall : Code := .call (ProgramLinking.liftProgram LeafStatisticsProgram.Finalize.program r3 finish)
def parameterCall : Code := .call (ProgramLinking.liftProgram LeafParametersProgram.Execute.program r9 bank)

theorem earlyCall_eval (a : Data) (ambient : List Bool)
    (hp : projectState r8 early a = LeafParametersProgram.Bank.state (a.regs ∘ r8)
      (EarlyThreshold.inputWords ambient)) :
    ∃ n ≤ EarlyThreshold.runtimeBound ambient, ∃ rf w,
      Eval earlyCall n a (embedState r8 early a (LeafParametersProgram.Bank.state rf w)) ∧
      BinaryArithmetic.toNat (w 16) = EarlyThreshold.threshold (BinaryArithmetic.toNat ambient) ∧
      w 0 = ambient ∧ (∀ j, j≠0 → j≠13 → j≠16 → w j=[]) := by
  obtain ⟨rf,w,he,hv,h0,hz⟩ := EarlyThreshold.input_program_runs ambient (a.regs ∘ r8)
  rw [←hp] at he
  obtain ⟨n,hn,he⟩ := call_run _ r8 early (registers_injective ..) (block_injective ..) a _ _ he
  exact ⟨n,hn,rf,w,he,hv,h0,hz⟩

theorem highCall_eval (a : Data) (rows : List (List ℕ)) (ambient tau : List Bool)
    (hn : 0 < BinaryArithmetic.toNat ambient)
    (hp : projectState r10 high a = HighIncidenceProgram.Prepare.initial (a.regs ∘ r10) rows ambient tau) :
    ∃ n ≤ HighIncidenceProgram.Prepare.budget rows ambient tau+1, ∃ b,
      Eval highCall n a (embedState r10 high a b) ∧
      b.stacks 14 = HighIncidenceProgram.highPrefix rows
        (HighIncidenceProgram.Prepare.cut rows ambient tau) (BinaryArithmetic.toNat ambient) ∧
      b.stacks 0 = LeafStatisticsProgram.scopeBits rows ∧
      b.stacks 16 = ambient ∧ b.stacks 17 = tau := by
  obtain ⟨n,b,he,hb,h0,h16,h17,h14,_⟩ := HighIncidenceProgram.Prepare.command_eval
    (a.regs ∘ r10) rows ambient tau hn
  have ht := compiled_halt_trace he 0 14
  rw [←hp] at ht
  have hrun := eval_call_from_state HighIncidenceProgram.Prepare.program r10 high a
    (registers_injective ..) (block_injective ..) ht
  exact ⟨n+1,by omega,b,hrun,h14,h0,h16,h17⟩

theorem maskCall_eval (a : Data) (descending : List Bool)
    (hp : projectState r2 mask a = HighIncidenceProgram.Mask.state (a.regs ∘ r2) descending [] [] []) :
    ∃ n ≤ 10*descending.length+9, ∃ rf,
      Eval maskCall n a (embedState r2 mask a
        (HighIncidenceProgram.Mask.state rf descending [] descending.reverse [])) := by
  obtain ⟨rf,he⟩ := HighIncidenceProgram.Mask.runsIn (a.regs ∘ r2) descending
  rw [←hp] at he
  obtain ⟨n,hn,he⟩ := call_run _ r2 mask (registers_injective ..) mask_injective a _ _ he
  exact ⟨n,hn,rf,he⟩

theorem statsCall_eval (a : Data) (rows : List (List ℕ)) (forward : List Bool)
    (hp : projectState r10 stats a = LeafStatisticsProgram.initial (a.regs ∘ r10) rows forward) :
    ∃ n ≤ LeafStatisticsProgram.bootBudget rows forward+
        LeafStatisticsProgram.variableBudget rows 0 forward+2, ∃ rf,
      Eval statsCall n a (embedState r10 stats a
        (LeafStatisticsProgram.variableState rf rows forward.length [] forward
          (LeafStatisticsProgram.variableTotals rows 0 forward LeafStatisticsProgram.zeroTotals))) := by
  obtain ⟨rf,he⟩ := LeafStatisticsProgram.program_runsIn (a.regs ∘ r10) rows forward
  rw [←hp] at he
  obtain ⟨n,hn,he⟩ := call_run _ r10 stats (registers_injective ..) (block_injective ..) a _ _ he
  exact ⟨n,hn,rf,he⟩

theorem arityCall_eval (a : Data) (rows : List (List ℕ)) (forward : List Bool)
    (hv : ∀ row ∈ rows, ∀ v ∈ row, v < forward.length)
    (hp : projectState r10 arity a = RecordPrograms.state LeafStatisticsProgram.Arity.ports
      (LeafStatisticsProgram.Arity.state (a.regs ∘ r10) forward [] [] [] 0 0)
      false true false (LeafStatisticsProgram.scopeBits rows) []) :
    ∃ n ≤ 4+RecordPrograms.budget (LeafStatisticsProgram.Arity.cost forward)
        (rows.map (Encoding.encodeList Encoding.encodeNat)), ∃ rf,
      Eval arityCall n a (embedState r10 arity a
        (LeafStatisticsProgram.Arity.state rf forward [] [] []
          (LeafStatisticsProgram.Arity.arity forward rows 0) rows.length)) := by
  obtain ⟨rf,he⟩ := LeafStatisticsProgram.Arity.program_runsIn (a.regs ∘ r10) forward rows hv
  change projectState r10 arity a = RecordPrograms.state LeafStatisticsProgram.Arity.ports
    (LeafStatisticsProgram.Arity.state (a.regs ∘ r10) forward [] [] [] 0 0) false true false
    (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) rows) [] at hp
  rw [←hp] at he
  obtain ⟨n,hn,he⟩ := call_run _ r10 arity (registers_injective ..) (block_injective ..) a _ _ he
  exact ⟨n,hn,rf,he⟩

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
