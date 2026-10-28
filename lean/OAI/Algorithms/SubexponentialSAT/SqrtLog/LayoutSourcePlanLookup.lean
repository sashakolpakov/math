import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookupPorts
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookupSemantics

namespace OAI.Algorithms

/-! Full pair-plan lookup at the source-row ABI. All query construction, record
comparison, index increments and cleanup are native paid instructions. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup
open SubexponentialSAT BitProgram StructuredCalls

/-- Includes the final halt instruction. -/
def pairBudget (literal ambient factor : ℕ) (ps : List (ℕ × ℕ)) : ℕ :=
  39*(literal+ambient+factor)+115+
    (36*(literal+ambient+factor)+179)*((LayoutOwnerFiberProgram.stream ps).length+1)

theorem pair_budget_eq (d : Native.Data) (ps : List (ℕ × ℕ)) (v n f : ℕ)
    (hv : d.stacks 233=unary v) (hn : d.stacks 212=unary n)
    (hf : d.stacks 216=unary f) :
    Native.budget d (records ps)+1=pairBudget v n f ps := by
  simp only [Native.budget,Local.budget,SubexpNodeIndexProgram.Internal.budget,
    hv,hn,hf,pairKey_length,List.length_append,List.length_replicate,records_stream,pairBudget]
  ring

theorem pair_command_eval (d : Native.Data) (ps : List (ℕ × ℕ)) (v n f : ℕ)
    (hv : d.stacks 233=unary v) (hn : d.stacks 212=unary n)
    (hf : d.stacks 216=unary f)
    (hmaster : d.stacks 337=LayoutOwnerFiberProgram.stream ps) (hc : Native.Clean d) :
    ∃ k, k+1 ≤ pairBudget v n f ps ∧ ∃ e : Native.Data,
      Eval Native.command k d e ∧
      e.stacks=Function.update d.stacks 304 (unary (ps.idxOf (v,n+f))) := by
  have hm : d.stacks 337=ProgramEncoding.encodeRecords (records ps) := by
    simpa only [records_stream] using hmaster
  obtain ⟨k,hk,e,he,hs⟩ := Native.command_eval d (records ps) hm hc
  have hu : unary n++unary f=unary (n+f) := (List.replicate_add n f true).symm
  rw [hv,hn,hf,hu,records_idxOf] at hs
  refine ⟨k,?_,e,he,hs⟩
  rw [←pair_budget_eq d ps v n f hv hn hf]
  omega

/-- Exact packed-row lookup from the actual plan stream. All master tapes and
all seven work tapes are preserved; only the initially empty row304 changes. -/
theorem pair_program_run (d : Native.Data) (ps : List (ℕ × ℕ)) (v n f : ℕ)
    (hv : d.stacks 233=unary v) (hn : d.stacks 212=unary n)
    (hf : d.stacks 216=unary f)
    (hmaster : d.stacks 337=LayoutOwnerFiberProgram.stream ps) (hc : Native.Clean d) :
    ∃ e : Native.Data,
      RunsIn Native.program (pairBudget v n f ps)
        (d.withPC (some Native.program.entry)) (e.withPC none) ∧
      e.stacks=Function.update d.stacks 304 (unary (ps.idxOf (v,n+f))) := by
  obtain ⟨k,hk,e,he,hs⟩ := pair_command_eval d ps v n f hv hn hf hmaster hc
  exact ⟨e,⟨k+1,hk,compiled_halt_trace he 233 304⟩,hs⟩

theorem pair_index_mem (ps : List (ℕ × ℕ)) (p : ℕ × ℕ) (h : p ∈ ps) :
    ps.idxOf p < ps.length ∧ ps[ps.idxOf p]?=some p := by
  constructor
  · simpa only [List.idxOf,beq_eq_decide] using List.idxOf_lt_length_iff.mpr h
  · simpa only [List.idxOf,beq_eq_decide] using List.getElem?_idxOf h

theorem pair_index_getElem (ps : List (ℕ × ℕ)) (h : ps.Nodup)
    (i : ℕ) (hi : i < ps.length) : ps.idxOf ps[i]=i := by
  simpa only [List.idxOf, beq_eq_decide] using h.idxOf_getElem i hi

/-- Coarse quadratic bound in the actual serialized input and unary query. -/
theorem pairBudget_polynomial (v n f : ℕ) (ps : List (ℕ × ℕ)) :
    pairBudget v n f ps ≤
      1000*((LayoutOwnerFiberProgram.stream ps).length+v+n+f+1)^2 := by
  unfold pairBudget
  nlinarith [sq_nonneg ((LayoutOwnerFiberProgram.stream ps).length : ℤ),
    sq_nonneg ((v+n+f : ℕ) : ℤ)]

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
