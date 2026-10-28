import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-! A fixed finite program removes the framing from a list of Boolean records.
The resulting packed array preserves both record order and bit order. -/

namespace SubexponentialSAT.SubexpRecordFlatten

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 5 4

def data (regs : Fin 5 → Bool) (source payload accumulator : List Bool) : Data :=
  ⟨regs, ![source, payload, accumulator, []]⟩

def ports : RecordPrograms.Ports 5 4 :=
  ⟨2, 3, 4, 0, 1, by decide, by decide, by decide, by decide⟩

def parserRegs (regs : Fin 5 → Bool) (v pr found : Bool) : Fin 5 → Bool :=
  Function.update (Function.update (Function.update regs 2 v) 3 pr) 4 found

theorem parser_data (regs : Fin 5 → Bool) (source payload acc src out : List Bool)
    (v pr found : Bool) :
    RecordPrograms.state ports (data regs source payload acc) v pr found src out =
      data (parserRegs regs v pr found) src out acc := by
  apply state_ext
  · rfl
  · funext i; fin_cases i <;> rfl

abbrev callback : Cmd 5 4 :=
  .seq (.call (StackRoutines.copyProgram 1 2 3 (0 : Fin 5) 1))
    (.call (StackRoutines.clearProgram 1 (0 : Fin 5) 1))

theorem callback_eval (regs : Fin 5 → Bool) (bits tail acc : List Bool) :
    Eval callback (9 * bits.length + 8)
      (data regs tail bits.reverse acc)
      (data (readRegs regs 0 1 none) tail [] (bits.reverse ++ acc)) := by
  have hc := copy_eval (data regs tail bits.reverse acc) 1 2 3 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  have he : afterCopy (data regs tail bits.reverse acc) 1 2 0 1 =
      data (readRegs regs 0 1 none) tail bits.reverse (bits.reverse ++ acc) := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [afterCopy, data, StackRoutines.copyStacks]
  rw [he] at hc
  have hclear := ListRegisterProgram.clear_run (1 : Fin 4) (0 : Fin 5) 1
    (readRegs regs 0 1 none)
    (data (readRegs regs 0 1 none) tail bits.reverse (bits.reverse ++ acc)).stacks
  have hf : Eval (.call (StackRoutines.clearProgram 1 (0 : Fin 5) 1))
      (2 * bits.length + 3)
      (data (readRegs regs 0 1 none) tail bits.reverse (bits.reverse ++ acc))
      (data (readRegs regs 0 1 none) tail [] (bits.reverse ++ acc)) := by
    have hst : StackRoutines.clearStacks (1 : Fin 4)
        ![tail, bits.reverse, bits.reverse ++ acc, []] =
        ![tail, [], bits.reverse ++ acc, []] := by
      funext i; fin_cases i <;> rfl
    apply Eval.call
    simpa [ListRegisterProgram.Run, data, hst,
      StackRoutines.readRegs_reset, StructuredProgram.State.withPC] using hclear
  have ht := hc.seq hf
  convert ht using 1
  all_goals simp [data]
  all_goals omega

def invariant (d : Data) : Prop := ∃ regs acc, d = data regs [] [] acc

def effect (bits : List Bool) (before after : Data) : Prop :=
  after.stacks 2 = bits.reverse ++ before.stacks 2

theorem callback_contract :
    RecordPrograms.CallbackContractWith ports callback (fun _ => false)
      (fun bits => 9 * bits.length + 8) invariant effect := by
  intro bits tail base hi
  obtain ⟨regs, acc, rfl⟩ := hi
  let rf := readRegs (parserRegs regs false true false) 0 1 none
  refine ⟨9 * bits.length + 8, data rf [] [] (bits.reverse ++ acc), le_rfl,
    ⟨rf, bits.reverse ++ acc, rfl⟩, rfl, ?_⟩
  rw [parser_data, parser_data]
  have hr : parserRegs rf false true false = rf := by
    funext i
    fin_cases i <;> simp [rf, parserRegs, readRegs]
  rw [hr]
  exact callback_eval _ _ _ _

theorem fold_reverse (records : List (List Bool)) (acc : List Bool) :
    records.foldl (fun a bits => bits.reverse ++ a) acc = records.flatten.reverse ++ acc := by
  induction records generalizing acc with
  | nil => rfl
  | cons bits rest ih =>
      simp only [List.foldl_cons, ih, List.flatten_cons, List.reverse_append, List.append_assoc]

theorem visits_output {records : List (List Bool)} {before after : Data}
    (h : RecordPrograms.Visits (fun _ => false) effect records before after) :
    after.stacks 2 = records.flatten.reverse ++ before.stacks 2 := by
  have hf := h.fold_of_false (by simp) (fun d => d.stacks 2)
    (fun acc bits => bits.reverse ++ acc) (by intro bits a b he; exact he)
  simpa only [fold_reverse] using hf

private theorem unread_false (records : List (List Bool)) :
    RecordPrograms.unread (fun _ => false) records [] = [] := by
  induction records <;> simp_all [RecordPrograms.unread]

private theorem budget_eq (records : List (List Bool)) :
    RecordPrograms.budget (fun bits => 9 * bits.length + 8) records =
      15 * (records.map List.length).sum + 15 * records.length := by
  induction records with
  | nil => rfl
  | cons bits rest ih => simp [RecordPrograms.budget, ih]; omega

theorem scan_eval (records : List (List Bool)) (regs : Fin 5 → Bool) :
    ∃ n rf, n ≤ 15 * (records.map List.length).sum + 15 * records.length + 3 ∧
      Eval (RecordPrograms.iterate ports callback) n
        (data regs (ProgramEncoding.encodeRecords records) [] [])
        (data rf [] [] records.flatten.reverse) := by
  let base := data regs [] [] []
  obtain ⟨n, next, hn, hi, hv, he⟩ := RecordPrograms.iterate_run_with
    ports callback (fun _ => false) (fun bits => 9 * bits.length + 8)
    invariant effect callback_contract records [] base ⟨regs, [], rfl⟩
    (regs 2) (regs 3) (regs 4)
  obtain ⟨nr, acc, rfl⟩ := hi
  have hout : acc = records.flatten.reverse := by
    simpa [base, data] using visits_output hv
  subst acc
  have hr : parserRegs regs (regs 2) (regs 3) (regs 4) = regs := by
    funext i; fin_cases i <;> simp [parserRegs]
  have hunread := unread_false records
  have hfinish : records.any (fun _ => false) = false := by simp
  have hb := budget_eq records
  refine ⟨n, parserRegs nr false true false, ?_, ?_⟩
  · simpa only [hb, Nat.add_comm 3] using hn
  · simpa only [base, parser_data, hr, hunread, hfinish, List.append_nil,
      ProgramEncoding.encodeRecords] using he

abbrev command : Cmd 5 4 :=
  .seq (RecordPrograms.iterate ports callback)
    (.call (StackRoutines.transferProgram 2 0 (0 : Fin 5) 1))

abbrev program : Program 5 4 (size command + 1) := compiled command 0 0

def bound (records : List (List Bool)) : ℕ :=
  18 * (records.map List.length).sum + 15 * records.length + 7

/-- A complete measured execution, including the parser and final reversal. -/
theorem program_run (records : List (List Bool)) (regs : Fin 5 → Bool) :
    ∃ rf, RunsIn program (bound records)
      ((data regs (ProgramEncoding.encodeRecords records) [] []).withPC (some program.entry))
      ((data rf records.flatten [] []).withPC none) := by
  obtain ⟨n, rf, hn, hs⟩ := scan_eval records regs
  have ht := transfer_eval (data rf [] [] records.flatten.reverse) 2 0 0 1
    (by decide) (by decide)
  have he : afterTransfer (data rf [] [] records.flatten.reverse) 2 0 0 1 =
      data (readRegs rf 0 1 none) records.flatten [] [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [afterTransfer, StackRoutines.transferStacks, data]
  rw [he] at ht
  have ht' : Eval (.call (StackRoutines.transferProgram 2 0 (0 : Fin 5) 1))
      (3 * records.flatten.length + 3)
      (data rf [] [] records.flatten.reverse)
      (data (readRegs rf 0 1 none) records.flatten [] []) := by
    simpa [data] using ht
  refine ⟨readRegs rf 0 1 none,
    n + (3 * records.flatten.length + 3) + 1, ?_, ?_⟩
  · have hl : records.flatten.length = (records.map List.length).sum := by simp
    unfold bound
    omega
  · exact compiled_halt_trace (hs.seq ht') (0 : Fin 4) 0

end SubexponentialSAT.SubexpRecordFlatten

end OAI.Algorithms
