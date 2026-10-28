import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgramSource

namespace OAI.Algorithms

/-! Complete preserving, paid lookup of a source clause by its list position. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Source
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives

abbrev copySource : Cmd 3 6 := .call (StackRoutines.copyProgram 0 1 4 0 1)
abbrev clearScan : Cmd 3 6 := .call (StackRoutines.clearProgram 1 0 1)
abbrev forward : Cmd 3 6 := .call (StackRoutines.transferProgram 3 5 0 1)
abbrev fetch : Cmd 3 6 := .seq copySource (.seq skipPrefix
  (.seq readSelected (.seq clearScan forward)))

theorem copySource_eval (v p f : Bool) (master index : List Bool) :
    Eval copySource (7*master.length+5)
      (data v p f master [] index [] [] [])
      (data false false f master master index [] [] []) := by
  have h := copy_eval (data v p f master [] index [] [] []) 0 1 4 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  convert h using 1
  · simp [data]
  · apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [data, ExecCNFRecords.regs, readRegs]
    · funext i; fin_cases i <;> simp [data, StackRoutines.copyStacks]

theorem clearScan_eval (v p f : Bool) (master rest payload : List Bool) :
    Eval clearScan (2*rest.length+3)
      (data v p f master rest [] payload [] [])
      (data false false f master [] [] payload [] []) := by
  have h := StackRoutines.clearProgram_trace (1 : Fin 6) (0 : Fin 3) 1
    (data v p f master rest [] payload [] []).regs
    (data v p f master rest [] payload [] []).stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  apply Eval.call
  convert hh using 1 <;>
    simp [StackRoutines.clearResult,
      StructuredProgram.State.withPC,data,
      StackRoutines.clearStacks,readRegs,Nat.add_assoc]
  all_goals funext i; fin_cases i <;> rfl

theorem forward_eval (v p f : Bool) (master bits : List Bool) :
    Eval forward (3*bits.length+3)
      (data v p f master [] [] bits.reverse [] [])
      (data false false f master [] [] [] [] bits) := by
  have h := transfer_eval (data v p f master [] [] bits.reverse [] []) 3 5 0 1
    (by decide) (by decide)
  convert h using 1
  · simp [data]
  · apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [data,ExecCNFRecords.regs,readRegs]
    · funext i; fin_cases i <;> simp [data,StackRoutines.transferStacks]

theorem fetch_eval (before : List (List Bool)) (bits rest : List Bool) (v p f : Bool) :
    let master := recordPrefix before ++ true :: (Encoding.frame bits ++ rest)
    Eval fetch (7*master.length+skipCost before+9*bits.length+2*rest.length+18)
      (data v p f master [] (Encoding.encodeNat before.length) [] [] [])
      (data false false (if before=[] then f else true) master [] [] [] [] bits) := by
  dsimp only
  let master := recordPrefix before ++ true :: (Encoding.frame bits ++ rest)
  have hc := copySource_eval v p f master (Encoding.encodeNat before.length)
  have hs := skipPrefix_eval before false false f master
    (true :: (Encoding.frame bits ++ rest)) [] [] []
  have hr := readSelected_eval false true (if before=[] then f else true) master bits rest []
  have hz := clearScan_eval false true (if before=[] then f else true) master rest bits.reverse
  have ht := forward_eval false false (if before=[] then f else true) master bits
  have h := hc.seq (hs.seq (hr.seq (hz.seq ht)))
  convert h using 1 ; simp only [master] ; omega

theorem recordPrefix_append (before after : List (List Bool)) :
    Encoding.encodeList id (before ++ after) = recordPrefix before ++ Encoding.encodeList id after := by
  induction before with
  | nil => rfl
  | cons b bs ih => simp [Encoding.encodeList,recordPrefix,ih,List.append_assoc]

theorem skipCost_le (before : List (List Bool)) : skipCost before ≤ 5*(recordPrefix before).length := by
  induction before with
  | nil => simp [skipCost,recordPrefix]
  | cons b bs ih =>
      simp only [skipCost,List.map_cons,List.sum_cons,recordPrefix,List.foldr_cons,
        List.length_cons,List.length_append] at *
      have hl : (Encoding.frame b).length=2*b.length+1 := Encoding.length_frame b
      omega

theorem fetch_cost_le (before : List (List Bool)) (bits rest : List Bool) :
    let master := recordPrefix before ++ true :: (Encoding.frame bits ++ rest)
    7*master.length+skipCost before+9*bits.length+2*rest.length+18 ≤
      23*master.length+18 := by
  have hs := skipCost_le before
  have hl : (Encoding.frame bits).length=2*bits.length+1 := Encoding.length_frame bits
  simp only [List.length_append,List.length_cons]
  omega

def fetchProgram := compiled fetch 2 5

/-- The source bytes are the original encoded list. The result is exactly the
indexed original payload, including order and repeated literals. -/
theorem fetch_original_runs (clauses : List (List Bool)) (i : Fin clauses.length)
    (v p f : Bool) :
    ∃ flag, RunsIn fetchProgram (23*(Encoding.encodeList id clauses).length+19)
      ((data v p f (Encoding.encodeList id clauses) []
        (Encoding.encodeNat i.val) [] [] []).withPC (some fetchProgram.entry))
      ((data false false flag (Encoding.encodeList id clauses) [] [] [] []
        clauses[i.val]).withPC none) := by
  let before := clauses.take i.val
  let rest := Encoding.encodeList id (clauses.drop (i.val+1))
  have hlen : before.length=i.val := by simp [before]
  have hsplit : Encoding.encodeList id clauses =
      recordPrefix before ++ true :: (Encoding.frame clauses[i.val] ++ rest) := by
    have h := List.take_append_drop i.val clauses
    rw [List.drop_eq_getElem_cons i.isLt] at h
    calc
      Encoding.encodeList id clauses = Encoding.encodeList id
          (clauses.take i.val ++ clauses[i.val] :: clauses.drop (i.val+1)) :=
        congrArg (Encoding.encodeList id) h.symm
      _ = _ := by rw [recordPrefix_append]; rfl
  have he := fetch_eval before clauses[i.val] rest v p f
  have hb := fetch_cost_le before clauses[i.val] rest
  dsimp only at he hb
  rw [← hsplit,hlen] at he
  rw [← hsplit] at hb
  refine ⟨if before=[] then f else true,?_,?_,?_⟩
  · exact 7*(Encoding.encodeList id clauses).length+skipCost before+
      9*clauses[i.val].length+2*rest.length+18+1
  · omega
  · exact compiled_halt_trace he 2 5

end SubexponentialSAT.SqrtLog.HashInputProgram.Source

end OAI.Algorithms
