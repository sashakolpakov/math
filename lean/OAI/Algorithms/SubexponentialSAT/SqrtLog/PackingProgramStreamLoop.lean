import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramStreams

namespace OAI.Algorithms

/-! The real dynamic loop over paired candidate counts. The pair list occurs
only in the input specification; the finite program reads runtime list tags. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Streams
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

 def pairsBytes : List (ℕ × ℕ) → List Bool
  | [] => [false]
  | p::ps => true :: (payload p ++ pairsBytes ps)
 def afterSource : List (ℕ × ℕ) → List Bool
  | [] => []
  | p::ps => payload p ++ pairsBytes ps
 def flag : List (ℕ × ℕ) → Bool
  | [] => false
  | _::_ => true
 def resultBody (wi wh : List Bool) : List (ℕ × ℕ) → List Bool
  | [] => []
  | p::ps => (true :: SubexponentialSAT.Encoding.frame (List.replicate (value wi wh p) false)) ++ resultBody wi wh ps
 def loopBudget (wi wh : List Bool) : List (ℕ × ℕ) → ℕ
  | [] => 1
  | p::ps => pairBudget wi wh p + loopBudget wi wh ps + 2

 theorem bytes_tag (ps : List (ℕ × ℕ)) : pairsBytes ps = flag ps :: afterSource ps := by
  cases ps <;> rfl

 def readTag : Cmd 8 12 := SubexponentialSAT.SubexpInputFrames.readTag 8
 def loop : Cmd 8 12 := .while 7 (.seq pairCommand readTag)

 theorem ready_update_source (regs : Fin 8 → Bool) (wi wh source tail acc output : List Bool) :
    Function.update (ready regs wi wh source acc output).stacks 8 tail =
      (ready regs wi wh tail acc output).stacks := by
  funext j
  fin_cases j <;> simp [ready,state]

 theorem tag_eval (regs : Fin 8 → Bool) (wi wh : List Bool) (ps : List (ℕ × ℕ))
    (acc output : List Bool) :
    ∃ rf, Eval readTag 1 (ready regs wi wh (pairsBytes ps) acc output)
      (ready rf wi wh (afterSource ps) acc output) ∧ rf 7 = flag ps := by
  obtain ⟨e, he, hs, hf⟩ := SubexponentialSAT.SubexpInputFrames.readTag_execute 8
    (ready regs wi wh (pairsBytes ps) acc output) (flag ps) (afterSource ps) (bytes_tag ps)
  have heq : e = ready e.regs wi wh (afterSource ps) acc output := by
    apply SubexponentialSAT.CounterForPrograms.data_ext <;> try rfl
    exact hs.trans (ready_update_source regs wi wh (pairsBytes ps) (afterSource ps) acc output)
  exact ⟨e.regs, eval_congr_output he heq, hf⟩

 theorem loop_eval (ps : List (ℕ × ℕ)) (regs : Fin 8 → Bool)
    (wi wh acc output : List Bool) (hf : regs 7 = flag ps) :
    ∃ n ≤ loopBudget wi wh ps, ∃ rf,
      Eval loop n (ready regs wi wh (afterSource ps) acc output)
        (ready rf wi wh [] ((resultBody wi wh ps).reverse ++ acc) output) := by
  induction ps generalizing regs acc with
  | nil =>
    exact ⟨1, le_rfl, regs, Eval.while_false hf⟩
  | cons p ps ih =>
    obtain ⟨n, hn, rp, hp⟩ := pairCommand_eval regs wi wh p (pairsBytes ps) acc output
    obtain ⟨rt, ht, hft⟩ := tag_eval rp wi wh ps
      (CandidateScoreProgram.reverseRecord (List.replicate (value wi wh p) false) acc) output
    obtain ⟨m, hm, rf, hr⟩ := ih rt
      (CandidateScoreProgram.reverseRecord (List.replicate (value wi wh p) false) acc) hft
    have h := Eval.while_true hf (hp.seq ht) hr
    refine ⟨n+1+m+1, by unfold loopBudget; omega, rf, ?_⟩
    simpa [loop,afterSource,resultBody,CandidateScoreProgram.reverseRecord,
      List.reverse_append,List.append_assoc] using h

 def finish : Cmd 8 12 := .seq (TupleProgram.pushConst 9 0 false)
  (.call (SubexponentialSAT.StackRoutines.transferProgram 9 10 0 1))
 def command : Cmd 8 12 := .seq readTag (.seq loop finish)
 def program := compiled command 8 10

 theorem finish_eval (regs : Fin 8 → Bool) (wi wh acc output : List Bool) :
    ∃ rf, Eval finish (3*acc.length+8) (ready regs wi wh [] acc output)
      (ready rf wi wh [] [] (acc.reverse ++ [false] ++ output)) := by
  let d := ready regs wi wh [] acc output
  let a := TupleProgram.pushedState 9 0 false d
  have hp := TupleProgram.pushConst_eval 9 0 false d
  have ht := SubexponentialSAT.SubexpScanPrimitives.transfer_eval a 9 10 0 1 (by decide) (by decide)
  have he : SubexponentialSAT.SubexpScanPrimitives.afterTransfer a 9 10 0 1 =
      ready (readRegs a.regs 0 1 none) wi wh [] [] (acc.reverse ++ [false] ++ output) := by
    apply SubexponentialSAT.CounterForPrograms.data_ext <;> try rfl
    funext j; fin_cases j <;>
      simp [SubexponentialSAT.SubexpScanPrimitives.afterTransfer,a,d,ready,state,
        SubexponentialSAT.StackRoutines.transferStacks,List.append_assoc]
  have ht' := eval_congr_output ht he
  refine ⟨readRegs a.regs 0 1 none, ?_⟩
  have h := hp.seq ht'
  convert h using 1 <;> simp [finish,a,d,ready,state] ; omega

 def scores (wi wh : List Bool) (ps : List (ℕ × ℕ)) : List (List Bool) :=
  ps.map (fun p => List.replicate (value wi wh p) false)

 theorem resultBody_records (wi wh : List Bool) (ps : List (ℕ × ℕ)) :
    resultBody wi wh ps ++ [false] = SubexponentialSAT.ProgramEncoding.encodeRecords (scores wi wh ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [resultBody,scores,List.map_cons,SubexponentialSAT.ProgramEncoding.encodeRecords,
      SubexponentialSAT.Encoding.encodeList,List.cons_append,List.append_assoc] at *
    rw [ih]
    rfl

 def streamBudget (wi wh : List Bool) (ps : List (ℕ × ℕ)) :=
  loopBudget wi wh ps + 3*(resultBody wi wh ps).length + 10

 theorem command_eval (regs : Fin 8 → Bool) (wi wh : List Bool) (ps : List (ℕ × ℕ)) :
    ∃ n ≤ streamBudget wi wh ps, ∃ rf,
      Eval command n (ready regs wi wh (pairsBytes ps) [] [])
        (ready rf wi wh [] [] (SubexponentialSAT.ProgramEncoding.encodeRecords (scores wi wh ps))) := by
  obtain ⟨rt, ht, hft⟩ := tag_eval regs wi wh ps [] []
  obtain ⟨n, hn, rl, hl⟩ := loop_eval ps rt wi wh [] [] hft
  simp only [List.append_nil] at hl
  obtain ⟨rf, hf⟩ := finish_eval rl wi wh (resultBody wi wh ps).reverse []
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil,resultBody_records] at hf
  refine ⟨1+(n+(3*(resultBody wi wh ps).length+8)), by unfold streamBudget; omega,
    rf, ht.seq (hl.seq hf)⟩

 theorem program_primitive (regs : Fin 8 → Bool) (wi wh : List Bool) (ps : List (ℕ × ℕ)) :
    ∃ rf, SubexponentialSAT.Computation.RunsIn (primitive program).step
      (primitiveOverhead program*(streamBudget wi wh ps+1))
      (primitiveCfg program ((ready regs wi wh (pairsBytes ps) [] []).withPC (some program.entry)))
      (primitiveCfg program ((ready rf wi wh [] []
        (SubexponentialSAT.ProgramEncoding.encodeRecords (scores wi wh ps))).withPC none)) := by
  obtain ⟨n, hn, rf, hr⟩ := command_eval regs wi wh ps
  exact ⟨rf, primitive_execution program ⟨n+1, by omega, compiled_halt_trace hr 8 10⟩⟩
end SubexponentialSAT.SqrtLog.PackingProgram.Streams

end OAI.Algorithms
