import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms

namespace OAI.Algorithms

/-! Read the actual Side record list to obtain its dimension, then square
that unary dimension for the basis-table generator. No cardinality or
square is supplied as an unverified runtime input. -/

namespace SubexponentialSAT.Subexp.ConstraintMatrixDimensions

open BitProgram StructuredCalls StackRoutines TupleProgram

abbrev Data := State 5 7

def recordPorts : RecordPrograms.Ports 5 7 :=
  ⟨0, 1, 2, 1, 2, by decide, by decide, by decide, by decide⟩

abbrev callback : Cmd 5 7 :=
  .seq (.call (clearProgram 2 3 4)) (pushConst 3 3 true)

def countInvariant (source : List Bool) (a : Data) : Prop :=
  a.stacks 0 = source ∧ a.stacks 4 = [] ∧ a.stacks 5 = [] ∧ a.stacks 6 = []

theorem callback_contract (source : List Bool) :
    RecordPrograms.CallbackContractWith recordPorts callback (fun _ => false)
      (fun bits => 2 * bits.length + 5) (countInvariant source)
      (fun _ a b => b.stacks 3 = true :: a.stacks 3) := by
  intro bits tail base hi
  let a := RecordPrograms.state recordPorts base false true false tail bits.reverse
  let b : Data := ⟨readRegs a.regs 3 4 none, clearStacks 2 a.stacks⟩
  let c := pushedState 3 3 true b
  have t0 := clear_eval (2 : Fin 7) (3 : Fin 5) 4 a
  have t1 := pushConst_eval (3 : Fin 7) (3 : Fin 5) true b
  have hc : RecordPrograms.state recordPorts c false true false tail [] = c := by
    apply RecordPrograms.state_eq_self <;>
      simp [c, b, a, readRegs, clearStacks, recordPorts, RecordPrograms.state]
  refine ⟨2 * bits.length + 5, c, le_rfl, ?_, ?_, ?_⟩
  · rcases hi with ⟨h0, h4, h5, h6⟩
    simp [countInvariant, c, b, a, clearStacks, recordPorts,
      RecordPrograms.state, h0, h4, h5, h6]
  · simp [c, b, a, clearStacks, recordPorts, RecordPrograms.state]
  · rw [hc]
    simpa [callback, c, a, b, recordPorts, RecordPrograms.state, Nat.add_assoc] using
      t0.seq t1

abbrev countCommand : Cmd 5 7 :=
  .seq (.call (copyProgram 0 1 5 3 4)) (RecordPrograms.iterate recordPorts callback)

def input (records : Records) (regs : Fin 5 → Bool) : Data :=
  ⟨regs, fun j => if j = 0 then ProgramEncoding.encodeRecords records else []⟩

def counted (records : Records) (regs : Fin 5 → Bool) : Data :=
  ⟨regs, fun j => if j = 0 then ProgramEncoding.encodeRecords records
    else if j = 3 then List.replicate records.length true else []⟩

def countBudget (records : Records) : ℕ :=
  7 * (ProgramEncoding.encodeRecords records).length + 8 +
    RecordPrograms.budget (fun bits => 2 * bits.length + 5) records

theorem fold_count (records : Records) (k : ℕ) :
    records.foldl (fun xs _ => true :: xs) (List.replicate k true) =
      List.replicate (k + records.length) true := by
  induction records generalizing k with
  | nil => simp
  | cons row rows ih =>
      change rows.foldl (fun xs _ => true :: xs) (List.replicate (k + 1) true) = _
      rw [ih]
      congr 1
      simp [Nat.add_comm, Nat.add_left_comm]

theorem count_eval (records : Records) (regs : Fin 5 → Bool) :
    ∃ n ≤ countBudget records, ∃ out,
      Eval countCommand n (input records regs) (counted records out) := by
  let a := input records regs
  let b : Data := ⟨readRegs a.regs 3 4 none, copyStacks 0 1 a.stacks⟩
  have t0 := copy_eval (0 : Fin 7) 1 5 (3 : Fin 5) 4
    (by decide) (by decide) (by decide) (by decide) a (by simp [a, input])
  have hb : countInvariant (ProgramEncoding.encodeRecords records) b := by
    simp [countInvariant, b, a, input, copyStacks]
  obtain ⟨n, next, hn, hi, history, he⟩ := RecordPrograms.iterate_run_with
    recordPorts callback (fun _ => false) (fun bits => 2 * bits.length + 5)
    (countInvariant (ProgramEncoding.encodeRecords records))
    (fun _ a b => b.stacks 3 = true :: a.stacks 3)
    (callback_contract _) records [] b hb (b.regs 0) (b.regs 1) (b.regs 2)
  have hstart : RecordPrograms.state recordPorts b (b.regs 0) (b.regs 1) (b.regs 2)
      (ProgramEncoding.encodeRecords records ++ []) [] = b := by
    apply RecordPrograms.state_eq_self <;> simp [recordPorts, b, a, input, copyStacks]
  have hout := history.fold_of_false (by simp) (fun a => a.stacks 3)
    (fun xs _ => true :: xs) (fun _ _ _ h => h)
  have hb3 : b.stacks 3 = List.replicate 0 true := by simp [b, a, input, copyStacks]
  change next.stacks 3 = records.foldl (fun xs _ => true :: xs) (b.stacks 3) at hout
  rw [hb3, fold_count] at hout
  simp only [Nat.zero_add] at hout
  let c := RecordPrograms.state recordPorts next false true false [] []
  have hc : c = counted records c.regs := by
    apply congrArg (StructuredProgram.State.mk c.regs)
    funext j
    rcases hi with ⟨h0, h4, h5, h6⟩
    fin_cases j <;> simp [recordPorts, h0, hout, h4, h5, h6]
  have he' : Eval (RecordPrograms.iterate recordPorts callback) n b c := by
    have hany : records.any (fun _ => false) = false := by simp only [List.any_eq_false]; simp
    change Eval (RecordPrograms.iterate recordPorts callback) n
      (RecordPrograms.state recordPorts b (b.regs 0) (b.regs 1) (b.regs 2)
        (ProgramEncoding.encodeRecords records ++ []) []) _ at he
    rw [hstart] at he
    simpa only [hany, unread_false, c] using he
  rw [hc] at he'
  refine ⟨7 * (ProgramEncoding.encodeRecords records).length + 5 + n, ?_, c.regs, ?_⟩
  · dsimp [countBudget]
    omega
  · simpa only [a, input, ite_true, countCommand] using t0.seq he'

def squarePorts : UnaryForPrograms.Ports 5 7 := ⟨6, 3, 4⟩
abbrev appendDimension : Cmd 5 7 := .call (copyProgram 3 4 5 3 4)
abbrev squareCommand : Cmd 5 7 := .seq (.call (copyProgram 3 6 5 3 4))
  (UnaryForPrograms.forCmd squarePorts appendDimension)

def squareInvariant (source : List Bool) (N k : ℕ) (a : Data) : Prop :=
  a.stacks 0 = source ∧ a.stacks 1 = [] ∧ a.stacks 2 = [] ∧
  a.stacks 3 = List.replicate N true ∧ a.stacks 4 = List.replicate (N * k) true ∧
  a.stacks 5 = []

theorem square_stable (source : List Bool) (N : ℕ) :
    UnaryForPrograms.FrameStable squarePorts (squareInvariant source N) := by
  intro k a b h ha
  rcases ha with ⟨h0, h1, h2, h3, h4, h5⟩
  exact ⟨(h 0 (by decide)).symm.trans h0, (h 1 (by decide)).symm.trans h1,
    (h 2 (by decide)).symm.trans h2, (h 3 (by decide)).symm.trans h3,
    (h 4 (by decide)).symm.trans h4, (h 5 (by decide)).symm.trans h5⟩

theorem square_body (source : List Bool) (N : ℕ) :
    UnaryForPrograms.BodySpec squarePorts appendDimension
      (squareInvariant source N) (fun _ => 7 * N + 5) := by
  intro k a ha
  rcases ha with ⟨h0, h1, h2, h3, h4, h5⟩
  let b : Data := ⟨readRegs a.regs 3 4 none, copyStacks 3 4 a.stacks⟩
  have he := copy_eval (3 : Fin 7) 4 5 (3 : Fin 5) 4
    (by decide) (by decide) (by decide) (by decide) a h5
  refine ⟨7 * N + 5, b, le_rfl, ?_, ?_, ?_⟩
  · simpa only [h3, List.length_replicate] using he
  · simp [b, squarePorts, copyStacks]
  · simp [squareInvariant, b, copyStacks, h0, h1, h2, h3, h4, h5,
      Nat.mul_add, Nat.add_comm]

def output (records : Records) (regs : Fin 5 → Bool) : Data :=
  ⟨regs, fun j => if j = 0 then ProgramEncoding.encodeRecords records
    else if j = 3 then List.replicate records.length true
    else if j = 4 then List.replicate (records.length * records.length) true else []⟩

theorem square_eval (records : Records) (regs : Fin 5 → Bool) :
    ∃ n ≤ 7 * records.length^2 + 14 * records.length + 7, ∃ out,
      Eval squareCommand n (counted records regs) (output records out) := by
  let a := counted records regs
  let b : Data := ⟨readRegs a.regs 3 4 none, copyStacks 3 6 a.stacks⟩
  have t0 := copy_eval (3 : Fin 7) 6 5 (3 : Fin 5) 4
    (by decide) (by decide) (by decide) (by decide) a (by simp [a, counted])
  have hb : squareInvariant (ProgramEncoding.encodeRecords records) records.length 0 b := by
    simp [squareInvariant, b, a, counted, copyStacks]
  obtain ⟨n, c, he, hc, hc6, hn⟩ := UnaryForPrograms.for_correct squarePorts appendDimension
    (squareInvariant (ProgramEncoding.encodeRecords records) records.length)
    (fun _ => 7 * records.length + 5) (square_stable _ _) (square_body _ _) b hb
  have hb6 : (b.stacks squarePorts.counter).length = records.length := by
    simp [b, a, squarePorts, counted, copyStacks]
  rw [hb6] at hc hn
  have hfinish : c = output records c.regs := by
    apply congrArg (StructuredProgram.State.mk c.regs)
    funext j
    rcases hc with ⟨h0, h1, h2, h3, h4, h5⟩
    have hc6' : c.stacks 6 = [] := hc6
    fin_cases j <;> simp [h0, h1, h2, h3, h4, h5, hc6']
  rw [hfinish] at he
  refine ⟨7 * records.length + 5 + n, ?_, c.regs, ?_⟩
  · rw [CounterForPrograms.budgetSum_const] at hn
    nlinarith only [hn]
  · simpa only [a, counted, copyStacks, ite_eq_right (by decide : (3 : Fin 7) ≠ 0),
      ite_eq_left rfl, ite_true, List.length_replicate, squareCommand] using t0.seq he

abbrev command : Cmd 5 7 := .seq countCommand squareCommand
def program := compiled command 0 4

def budget (records : Records) : ℕ :=
  countBudget records + 7 * records.length^2 + 14 * records.length + 8

theorem program_runsIn (records : Records) (regs : Fin 5 → Bool) :
    ∃ out, RunsIn program (budget records)
      ((input records regs).withPC (some program.entry))
      ((output records out).withPC none) := by
  obtain ⟨nc, hnc, cr, hc⟩ := count_eval records regs
  obtain ⟨ns, hns, sr, hs⟩ := square_eval records cr
  exact ⟨sr, nc + ns + 1, by dsimp [budget]; omega, compiled_halt_trace (hc.seq hs) 0 4⟩

end SubexponentialSAT.Subexp.ConstraintMatrixDimensions

end OAI.Algorithms
