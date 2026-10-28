import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramControllerGroup

namespace OAI.Algorithms

/-! A single finite bit program enumerates only head assignments, computes
exact labels, deduplicates attained keys and emits every nonempty bucket. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram.Controller
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- The finite command has no instance-dependent instructions. -/
def command : Code := .seq enumerate groupCommand
def program := compiled command 23 21

def initialState (regs : Fin 10 → Bool) (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h : ℕ) : Data :=
  input regs W (SubexponentialSAT.Subexp.MatrixProgramSupport.words (rows.map SubexponentialSAT.Subexp.MatrixProgramSupport.words))
    (HeadScatterProgram.indices js) (HeadScatterProgram.unary n) h

def finalState (regs : Fin 10 → Bool) (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h : ℕ) : Data :=
  state regs W (SubexponentialSAT.Subexp.MatrixProgramSupport.words (rows.map SubexponentialSAT.Subexp.MatrixProgramSupport.words))
    (HeadScatterProgram.indices js) (HeadScatterProgram.unary n) [] [] []
    (tableOutput (labelledRecords W rows js n h)) [] []

def cleanupCost (records : List Record) : ℕ :=
  2*(SubexponentialSAT.Subexp.BucketProgram.encodeRecords records.reverse).length+8

def groupCost (W : List Bool) (rows : List (List (List Bool))) (js : List ℕ) (n h : ℕ) : ℕ :=
  Label.cost W rows js n (assignments h)+2 + dedupCost (labelledRecords W rows js n h) +
  SubexponentialSAT.Subexp.PackingBucketTable.budget (labelledRecords W rows js n h)
    (keys (labelledRecords W rows js n h)) + cleanupCost (labelledRecords W rows js n h)

def cost (W : List Bool) (rows : List (List (List Bool))) (js : List ℕ) (n h : ℕ) : ℕ :=
  enumerateCost h + groupCost W rows js n h + 1

theorem groupCommand_eval (regs : Fin 10 → Bool) (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h : ℕ) (hrows : ∀ row∈rows,row.length=h)
    (hlen : js.length=h) (hjs : ∀ j∈js,j < n) :
    ∃ t ≤ groupCost W rows js n h, ∃ rf,
      Eval groupCommand t (labelInput regs W rows js n h) (finalState rf W rows js n h) := by
  obtain ⟨a,ha,ra,hea⟩ := label_eval regs W rows js n h hrows hlen hjs
  obtain ⟨b,hb,rb,heb⟩ := dedup_eval ra W rows js n (labelledRecords W rows js n h)
  obtain ⟨c,hc,rc,hec⟩ := group_eval rb W rows js n (labelledRecords W rows js n h)
  let d := labelledState rc W rows js n (labelledRecords W rows js n h) []
    (tableOutput (labelledRecords W rows js n h))
  have hed := WorkspaceCleanupProgram.command_eval (0 : Fin 10) 1
    ([15,19] : List (Fin 24)) (by decide) d
  have hs : WorkspaceCleanupProgram.finish (0 : Fin 10) 1 ([15,19] : List (Fin 24)) d =
      finalState (WorkspaceCleanupProgram.finish 0 1 ([15,19] : List (Fin 24)) d).regs W rows js n h := by
    apply congrArg (StructuredProgram.State.mk _)
    funext i; fin_cases i <;> simp [d,labelledState,state,BankRoutines.clearBankStacks]
  rw [hs] at hed
  refine ⟨a+(b+(c+WorkspaceCleanupProgram.cost ([15,19] : List (Fin 24)) d)),?_,(WorkspaceCleanupProgram.finish 0 1 ([15,19] : List (Fin 24)) d).regs,?_⟩
  · simp [WorkspaceCleanupProgram.cost,d,labelledState,state,groupCost,cleanupCost]
    omega
  · exact hea.seq (heb.seq (hec.seq hed))

theorem command_eval (regs : Fin 10 → Bool) (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h : ℕ) (hrows : ∀ row∈rows,row.length=h)
    (hlen : js.length=h) (hjs : ∀ j∈js,j < n) :
    ∃ t < cost W rows js n h, ∃ rf,
      Eval command t (initialState regs W rows js n h) (finalState rf W rows js n h) := by
  obtain ⟨a,ha,ra,hea⟩ := enumerate_eval regs W
    (SubexponentialSAT.Subexp.MatrixProgramSupport.words (rows.map SubexponentialSAT.Subexp.MatrixProgramSupport.words))
    (HeadScatterProgram.indices js) (HeadScatterProgram.unary n) h
  obtain ⟨b,hb,rb,heb⟩ := groupCommand_eval ra W rows js n h hrows hlen hjs
  exact ⟨a+b,by dsimp [cost]; omega,rb,hea.seq heb⟩

theorem program_runsIn (regs : Fin 10 → Bool) (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h : ℕ) (hrows : ∀ row∈rows,row.length=h)
    (hlen : js.length=h) (hjs : ∀ j∈js,j < n) :
    ∃ rf, RunsIn program (cost W rows js n h)
      ((initialState regs W rows js n h).withPC (some program.entry))
      ((finalState rf W rows js n h).withPC none) := by
  obtain ⟨t,ht,rf,he⟩ := command_eval regs W rows js n h hrows hlen hjs
  exact ⟨rf,t+1,by omega,compiled_halt_trace he 23 21⟩

theorem program_primitive (regs : Fin 10 → Bool) (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h : ℕ) (hrows : ∀ row∈rows,row.length=h)
    (hlen : js.length=h) (hjs : ∀ j∈js,j < n) :
    ∃ rf, SubexponentialSAT.Computation.RunsIn (primitive program).step
      (primitiveOverhead program * cost W rows js n h)
      (primitiveCfg program ((initialState regs W rows js n h).withPC (some program.entry)))
      (primitiveCfg program ((finalState rf W rows js n h).withPC none)) := by
  obtain ⟨rf,he⟩ := program_runsIn regs W rows js n h hrows hlen hjs
  exact ⟨rf,primitive_execution program he⟩

end SubexponentialSAT.SqrtLog.BucketProgram.Controller

end OAI.Algorithms
