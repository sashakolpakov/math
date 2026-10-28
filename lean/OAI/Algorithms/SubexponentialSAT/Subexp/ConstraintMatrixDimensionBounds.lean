import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintMatrixDimensions

namespace OAI.Algorithms

/-! A polynomial cap for the actual record-counting and unary-squaring
program used before local basis search. -/

namespace SubexponentialSAT.Subexp.ConstraintMatrixDimensions

open BitProgram

theorem callback_budget_eq (records : List (List Bool)) :
    RecordPrograms.budget (fun bits => 2 * bits.length + 5) records =
      8 * (records.map List.length).sum + 12 * records.length := by
  induction records with
  | nil => simp [RecordPrograms.budget]
  | cons row rows ih =>
      simp only [RecordPrograms.budget, ih, List.map_cons, List.sum_cons, List.length_cons]
      ring

theorem budget_le_length (records : List (List Bool)) :
    budget records ≤ 32 * ((ProgramEncoding.encodeRecords records).length + 1)^2 := by
  let L := (ProgramEncoding.encodeRecords records).length
  have hL : L = 2 * (records.map List.length).sum + 2 * records.length + 1 :=
    ProgramEncoding.encodeRecords_length records
  have hn : records.length ≤ L := by omega
  have hs : (records.map List.length).sum ≤ L := by omega
  have hn2 : records.length^2 ≤ L^2 := Nat.pow_le_pow_left hn 2
  change budget records ≤ 32 * (L + 1)^2
  rw [budget, countBudget, callback_budget_eq]
  change 7 * L + 8 + (8 * (records.map List.length).sum + 12 * records.length) +
    7 * records.length^2 + 14 * records.length + 8 ≤ _
  nlinarith only [hn, hs, hn2]

theorem program_runsIn_quadratic (records : List (List Bool)) (regs : Fin 5 → Bool) :
    ∃ out, RunsIn program (32 * ((ProgramEncoding.encodeRecords records).length + 1)^2)
      ((input records regs).withPC (some program.entry)) ((output records out).withPC none) := by
  obtain ⟨out, n, hn, ht⟩ := program_runsIn records regs
  exact ⟨out, n, hn.trans (budget_le_length records), ht⟩

end SubexponentialSAT.Subexp.ConstraintMatrixDimensions

end OAI.Algorithms
