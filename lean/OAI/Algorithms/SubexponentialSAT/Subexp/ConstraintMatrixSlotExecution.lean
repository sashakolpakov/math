import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintMatrixSlot

namespace OAI.Algorithms

/-! Complete actual emission of one slot's Joint rows, including the
physical row counter and ordered matrix-byte accumulation. -/

namespace SubexponentialSAT.Subexp.ConstraintMatrixSlot

open BitProgram StructuredCalls MatrixWordEncoding MulticolorTypes

variable {r Q Δ : ℕ}

def rowsBytes (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q) (xs : List (ZMod p))
    (rows columns : List (UniversalType r Q Δ)) : List Bool :=
  rows.flatMap fun u => ConstraintMatrixRow.rowBytes p i t u xs columns

theorem visits_output (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q) (xs : List (ZMod p))
    (rows columns : List (UniversalType r Q Δ)) {a b : Data}
    (h : RecordPrograms.Visits (fun _ => false) (effect p i t xs columns)
      (rows.map CollisionProgram.encodeType) a b) :
    b.stacks 50 = (rowsBytes p i t xs rows columns).reverse ++ a.stacks 50 ∧
    b.stacks 55 = List.replicate rows.length true ++ a.stacks 55 := by
  induction rows generalizing a b with
  | nil =>
      cases h
      simp [rowsBytes]
  | cons u us ih =>
      cases h with
      | hit ht he => contradiction
      | miss ht he history =>
          obtain ⟨hbytes, hcount⟩ := ih history
          constructor
          · rw [hbytes, he.1 u rfl]
            simp [rowsBytes, List.reverse_append, List.append_assoc]
          · rw [hcount, he.2]
            simp [List.replicate_add, List.append_assoc]

def state (ctx : Fin 51 → List Bool) (regs : Fin 16 → Bool)
    (source columns accumulator counter : List Bool) : Data :=
  ⟨regs, fun j => if h : j.val < 51 then
      if j = 50 then accumulator else ctx ⟨j.val, h⟩
    else if j = 51 then source else if j = 53 then columns
    else if j = 55 then counter else []⟩

theorem state_low (ctx : Fin 51 → List Bool) (regs : Fin 16 → Bool)
    (source columns accumulator counter : List Bool) (j : Fin 51) (hj : j ≠ 50) :
    (state ctx regs source columns accumulator counter).stacks (rowPorts j) = ctx j := by
  have hn : rowPorts j ≠ 50 := fun h =>
    hj (Fin.ext (congrArg (fun k : Fin 56 => k.val) h))
  change (Fin.castAdd 5 j : Fin 56) ≠ 50 at hn
  simp [state, rowPorts, j.isLt, hn]

theorem state_invariant (ctx : Fin 51 → List Bool) (regs : Fin 16 → Bool)
    (source columns accumulator counter : List Bool) :
    invariant ctx columns (state ctx regs source columns accumulator counter) := by
  exact ⟨fun j hj => state_low ctx regs source columns accumulator counter j hj,
    rfl, rfl⟩

theorem record_budget (p E N C : ℕ) (rows : List (UniversalType r Q Δ)) :
    RecordPrograms.budget (callbackCost p E N C r Q Δ) (rows.map CollisionProgram.encodeType) =
      rows.length * (ConstraintMatrixRow.budget p E N r Q Δ +
        11 * CollisionProgram.typeWidth r Q Δ + 7 * C + 20) := by
  induction rows with
  | nil => simp [RecordPrograms.budget]
  | cons u us ih =>
      simp only [List.map_cons, RecordPrograms.budget, callbackCost,
        CollisionProgram.encodeType_length, ih, List.length_cons]
      ring

def budget (p E N C R r Q Δ : ℕ) : ℕ :=
  R * (ConstraintMatrixRow.budget p E N r Q Δ +
    11 * CollisionProgram.typeWidth r Q Δ + 7 * C + 20) + 4

theorem program_runsIn (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (i : Fin Δ) (t : Fin Q) (anchor : UniversalType r Q Δ) (xs : List (ZMod p))
    (rows columns : List (UniversalType r Q Δ)) (E : ℕ)
    (hE : ∀ u ∈ rows, ∀ y ∈ columns, ConstraintEntryProgram.programBudget p i t u y xs ≤ E)
    (regs : Fin 16 → Bool) (accumulator counter : List Bool) :
    ∃ out, RunsIn program
      (budget p E columns.length
        (ProgramEncoding.encodeRecords (columns.map CollisionProgram.encodeType)).length
        rows.length r Q Δ)
      ((state (context p i t anchor xs) regs
        (ProgramEncoding.encodeRecords (rows.map CollisionProgram.encodeType))
        (ProgramEncoding.encodeRecords (columns.map CollisionProgram.encodeType))
        accumulator counter).withPC (some program.entry))
      ((state (context p i t anchor xs) out []
        (ProgramEncoding.encodeRecords (columns.map CollisionProgram.encodeType))
        ((rowsBytes p i t xs rows columns).reverse ++ accumulator)
        (List.replicate rows.length true ++ counter)).withPC none) := by
  let ctx := context p i t anchor xs
  let records := rows.map CollisionProgram.encodeType
  let colBytes := ProgramEncoding.encodeRecords (columns.map CollisionProgram.encodeType)
  let base := state ctx regs (ProgramEncoding.encodeRecords records) colBytes accumulator counter
  have hv : ∀ bits ∈ records, validPayload p i t xs columns E bits := by
    intro bits hb
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hb
    exact ⟨u, rfl, hE u hu⟩
  obtain ⟨n, next, hn, hi, history, he⟩ := RecordPrograms.iterate_run_with_on
    recordPorts callback (fun _ => false)
    (callbackCost p E columns.length colBytes.length r Q Δ) (invariant ctx colBytes)
    (effect p i t xs columns) (validPayload p i t xs columns E)
    (callback_contract p h2 i t anchor xs columns E) records [] base hv
    (state_invariant _ _ _ _ _ _) (base.regs 13) (base.regs 14) (base.regs 15)
  have hstart : RecordPrograms.state recordPorts base (base.regs 13) (base.regs 14)
      (base.regs 15) (ProgramEncoding.encodeRecords records ++ []) [] = base := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · change ProgramEncoding.encodeRecords records = ProgramEncoding.encodeRecords records ++ []
      simp only [List.append_nil]
    · rfl
  obtain ⟨hbytes, hcount⟩ := visits_output p i t xs rows columns history
  let last := RecordPrograms.state recordPorts next false true false [] []
  have hfinish : last = state ctx last.regs [] colBytes
      ((rowsBytes p i t xs rows columns).reverse ++ accumulator)
      (List.replicate rows.length true ++ counter) := by
    apply congrArg (StructuredProgram.State.mk last.regs)
    funext j
    rcases hi with ⟨hctx, h53, h54⟩
    by_cases hj : j.val < 51
    · by_cases hj50 : j = 50
      · subst j
        simp [recordPorts, state, hbytes, base]
      · have hj51 : j ≠ 51 := by
          intro h; subst j; change 51 < 51 at hj; omega
        have hj52 : j ≠ 52 := by
          intro h; subst j; change 52 < 51 at hj; omega
        have hn : (⟨j.val, hj⟩ : Fin 51) ≠ 50 := by
          intro h
          apply hj50
          exact Fin.ext (congrArg (fun k : Fin 51 => k.val) h)
        have hl := hctx ⟨j.val, hj⟩ hn
        have hid : rowPorts ⟨j.val, hj⟩ = j := Fin.ext rfl
        rw [hid] at hl
        simpa [last, RecordPrograms.state, recordPorts, state, hj, hj50, hj51, hj52] using hl
    · have hcases : j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨ j = 55 := by
        have hlt := j.isLt
        simp only [Fin.ext_iff]
        omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl <;>
        simp [recordPorts, state, h53, h54, hcount, base]
  have he' : Eval command n base last := by
    have hany : records.any (fun _ => false) = false := by simp only [List.any_eq_false]; simp
    change Eval command n
      (RecordPrograms.state recordPorts base (base.regs 13) (base.regs 14)
        (base.regs 15) (ProgramEncoding.encodeRecords records ++ []) []) _ at he
    rw [hstart] at he
    simpa only [hany, last, TupleProgram.unread_false] using he
  rw [hfinish] at he'
  refine ⟨last.regs, n + 1, ?_, compiled_halt_trace he' 51 50⟩
  change n ≤ 3 + RecordPrograms.budget (callbackCost p E columns.length colBytes.length r Q Δ)
    (rows.map CollisionProgram.encodeType) at hn
  rw [record_budget] at hn
  dsimp only [colBytes] at hn
  dsimp [budget, colBytes]
  omega

end SubexponentialSAT.Subexp.ConstraintMatrixSlot

end OAI.Algorithms
