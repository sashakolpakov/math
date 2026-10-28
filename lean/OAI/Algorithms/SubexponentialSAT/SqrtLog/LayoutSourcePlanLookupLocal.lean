import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookupQuery
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookupScan

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

namespace Local

def command : Code := .seq buildQuery (.seq Scan.command (clear 6))

def budget (literal ambient factor : List Bool) (nodes : List (List Bool)) : ℕ :=
  39*(literal.length+ambient.length+factor.length)+113+
    SubexpNodeIndexProgram.Internal.budget (pairKey literal (ambient++factor)) nodes

/-- An actual full-pair record search, including query construction and cleanup. -/
theorem command_eval (regs : Fin 16 → Bool) (literal ambient factor : List Bool)
    (nodes : List (List Bool)) :
    ∃ n ≤ budget literal ambient factor nodes, ∃ rf,
      Eval command n
        (data regs literal ambient factor (ProgramEncoding.encodeRecords nodes)
          [] [] [] [] [] [] [] [])
        (data rf literal ambient factor (ProgramEncoding.encodeRecords nodes)
          (List.replicate (nodes.idxOf (pairKey literal (ambient++factor))) true)
          [] [] [] [] [] [] []) := by
  obtain ⟨r1,h1⟩ := buildQuery_eval regs literal ambient factor (ProgramEncoding.encodeRecords nodes)
  obtain ⟨n,hn,r2,h2⟩ := Scan.command_eval r1 literal ambient factor
    (pairKey literal (ambient++factor)) nodes
  let q := pairKey literal (ambient++factor)
  let count := List.replicate (nodes.idxOf q) true
  let d := data r2 literal ambient factor (ProgramEncoding.encodeRecords nodes)
    count [] q [] [] [] [] []
  have h3 := clear_eval 6 d
  have he : (⟨readRegs d.regs 0 1 none,Function.update d.stacks 6 []⟩ : Data)=
      data (readRegs r2 0 1 none) literal ambient factor (ProgramEncoding.encodeRecords nodes)
        count [] [] [] [] [] [] [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [d,data]
  rw [he] at h3
  refine ⟨31*(literal.length+ambient.length+factor.length)+88+
    (n+(2*q.length+3)),?_,readRegs r2 0 1 none,?_⟩
  · simp only [budget,q,pairKey_length,List.length_append] at *
    omega
  · exact h1.seq (h2.seq h3)

end Local
end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
