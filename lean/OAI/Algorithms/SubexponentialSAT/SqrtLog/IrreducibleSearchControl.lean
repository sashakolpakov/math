import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchSelection
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchProgram

namespace OAI.Algorithms

/-! Exact output of the fixed first-success record iterator. The measured
callback contract is discharged by the concrete coefficient checker. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open BitProgram StructuredCalls SubexpEnumerationPayload SubexpTupleRefinement

/-- The visiting semantics stores the first successful record, including order. -/
theorem selected_of_visits_find {r s : ℕ} (output : Fin s)
    (test : List Bool → Bool) {records : List (List Bool)} {base next : State r s}
    (h : RecordPrograms.Visits test (fun bits _ b => b.stacks output = bits) records base next)
    {bits : List Bool} (hf : records.find? test = some bits) :
    next.stacks output = bits := by
  induction h with
  | nil base => simp at hf
  | @hit word rest base next ht he =>
      have hb : word = bits := by simpa [ht] using hf
      simpa only [hb] using he
  | @miss word rest base middle next ht he history ih =>
      exact ih (by simpa [ht] using hf)

/-- The generic measured iterator returns precisely the original selected
coefficient vector when its concrete callback agrees with `passes`. -/
theorem encoded_searchCommand_eval {r s d : ℕ} (hd : 0 < d)
    (p : RecordPrograms.Ports r s) (predicate : Cmd r s) (output : Fin s)
    (test : List Bool → Bool) (cost : List Bool → ℕ)
    (invariant : State r s → Prop) (valid : List Bool → Prop)
    (contract : RecordPrograms.CallbackContractWithOn p predicate test cost invariant
      (fun bits _ b => b.stacks output = bits) valid)
    (hcheck : ∀ c : Fin d → F, test (encodeTuple (scalarCode 3) c) = passes c)
    (suffix : List Bool) (base : State r s)
    (hvalid : ∀ c : Fin d → F, valid (encodeTuple (scalarCode 3) c))
    (hbase : invariant base) (v pr result : Bool) :
    ∃ n next,
      n ≤ 3 + RecordPrograms.budget cost
        ((candidates d).map (encodeTuple (scalarCode 3))) ∧
      invariant next ∧
      next.stacks output = encodeTuple (scalarCode 3) (coefficients d) ∧
      Eval (Subexp.BlockSearchProgram.anyCommand p predicate) n
        (RecordPrograms.state p base v pr result
          (ProgramEncoding.encodeRecords
            ((candidates d).map (encodeTuple (scalarCode 3))) ++ suffix) [])
        (RecordPrograms.state p next false true true
          (RecordPrograms.unread test
            ((candidates d).map (encodeTuple (scalarCode 3))) suffix) []) := by
  let records := (candidates d).map (encodeTuple (scalarCode 3))
  have hf : records.find? test =
      some (encodeTuple (scalarCode 3) (coefficients d)) :=
    find_encoded_eq_coefficients hd test hcheck
  have hr : ∀ bits ∈ records, valid bits := by
    intro bits hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    exact hvalid c
  have hany : records.any test = true := by
    apply List.any_eq_true.mpr
    exact ⟨_, List.mem_of_find?_eq_some hf, List.find?_some hf⟩
  obtain ⟨n, next, hn, hnext, history, run⟩ := RecordPrograms.iterate_run_with_on
    p predicate test cost invariant (fun bits _ b => b.stacks output = bits) valid
    contract records suffix base hr hbase v pr result
  refine ⟨n, next, hn, hnext, selected_of_visits_find output test history hf, ?_⟩
  simpa only [Subexp.BlockSearchProgram.anyCommand, hany] using run

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
