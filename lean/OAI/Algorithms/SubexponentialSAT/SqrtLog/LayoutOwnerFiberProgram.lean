import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgramLoop

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def copySource : Code := .call (StackRoutines.copyProgram 1 2 6 0 1)
def restore : Code := .call (StackRoutines.transferProgram 8 10 0 1)
def command : Code := .seq copySource (.seq scan (.seq (clear 7) restore))
def program := compiled command 0 10

def budget (query : ℕ) (ps : List (ℕ × ℕ)) : ℕ :=
  7*(stream ps).length+scanCost query 0 ps+2*ps.length+
    3*(encodeIndices (fiberIndices query 0 ps)).length+13

theorem command_eval (query : ℕ) (ps : List (ℕ × ℕ)) (regs : Fin 5 → Bool) :
    ∃ n < budget query ps, ∃ rf,
      Eval command n (data regs (unary query) (stream ps) [] [] [] [] [] [] [] [] [])
        (data rf (unary query) (stream ps) [] [] [] [] [] [] []
          (unary (fiberIndices query 0 ps).length) (encodeIndices (fiberIndices query 0 ps))) := by
  let a := data regs (unary query) (stream ps) [] [] [] [] [] [] [] [] []
  have h1 := copy_eval a 1 2 6 0 1 (by decide) (by decide) (by decide) (by decide) rfl
  have he1 : afterCopy a 1 2 0 1=
      data (status regs false false) (unary query) (stream ps) (stream ps) [] [] [] [] [] [] [] [] := by
    apply state_ext
    · simp [afterCopy,a,data]
    · funext i; fin_cases i <;> simp [afterCopy,a,data,StackRoutines.copyStacks]
  rw [he1] at h1
  obtain ⟨n,hn,rr,h2⟩ := scan_eval ps query 0 0 (status regs false false) (stream ps) [] []
  simp only [Nat.zero_add,List.replicate_zero,List.append_nil] at h2
  let bits := encodeIndices (fiberIndices query 0 ps)
  have h3 := clear_eval 7 (data rr (unary query) (stream ps) [] [] [] [] []
    (unary ps.length) bits.reverse (unary (fiberIndices query 0 ps).length) [])
  have he3 : cleared (data rr (unary query) (stream ps) [] [] [] [] []
      (unary ps.length) bits.reverse (unary (fiberIndices query 0 ps).length) []) 7=
      data (status rr false false) (unary query) (stream ps) [] [] [] [] [] []
        bits.reverse (unary (fiberIndices query 0 ps).length) [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [cleared,data]
  rw [he3] at h3
  let b := data (status rr false false) (unary query) (stream ps) [] [] [] [] [] []
    bits.reverse (unary (fiberIndices query 0 ps).length) []
  have h4 := transfer_eval b 8 10 0 1 (by decide) (by decide)
  have he4 : afterTransfer b 8 10 0 1=
      data (status rr false false) (unary query) (stream ps) [] [] [] [] [] [] []
        (unary (fiberIndices query 0 ps).length) bits := by
    apply state_ext
    · simp [afterTransfer,b,data]
    · funext i; fin_cases i <;> simp [afterTransfer,b,data,StackRoutines.transferStacks]
  rw [he4] at h4
  have hh := h1.seq (h2.seq (h3.seq h4))
  refine ⟨7*(stream ps).length+5+(n+(2*ps.length+3+(3*bits.length+3))),?_,
    status rr false false,?_⟩
  · unfold budget
    dsimp only [bits]
    omega
  · simpa [command,copySource,restore,a,b,data,bits] using hh

/-- Source and original query are preserved. Output10 is the raw concatenation
of canonical incidence-index fields, with no list or frame oracle supplied. -/
theorem program_runs (query : ℕ) (ps : List (ℕ × ℕ)) (regs : Fin 5 → Bool) :
    ∃ rf, RunsIn program (budget query ps)
      ((data regs (unary query) (stream ps) [] [] [] [] [] [] [] [] []).withPC (some program.entry))
      ((data rf (unary query) (stream ps) [] [] [] [] [] [] []
        (unary (fiberIndices query 0 ps).length) (encodeIndices (fiberIndices query 0 ps))).withPC none) := by
  obtain ⟨n,hn,rf,he⟩ := command_eval query ps regs
  exact ⟨rf,n+1,by omega,compiled_halt_trace he 0 10⟩

theorem stream_original (ps : List (ℕ × ℕ)) :
    stream ps=ProgramEncoding.encodeRecords
      (ps.map fun p => SubexponentialSAT.Subexp.PackingVertexLabels.planPayload [p.1,p.2]) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simpa only [stream,ProgramEncoding.encodeRecords,List.map_cons,Encoding.encodeList,
        pairPayload_original, Function.id_def] using congrArg
          (fun tail => true::(Encoding.frame (pairPayload p.1 p.2)++tail)) ih

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
