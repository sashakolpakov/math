import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintMatrixRow

namespace OAI.Algorithms

/-! The complete fixed row iterator, with its actual ordered scalar output. -/

namespace SubexponentialSAT.Subexp.ConstraintMatrixRow

open BitProgram StructuredCalls MatrixWordEncoding MulticolorTypes

variable {r Q Δ : ℕ}

def rowBytes (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q)
    (u : UniversalType r Q Δ) (xs : List (ZMod p)) (columns : List (UniversalType r Q Δ)) :
    List Bool := columns.flatMap fun y =>
      Encoding.frame (word p (ConstraintEntryProgram.value p i t u y xs))

theorem visits_output (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q)
    (u : UniversalType r Q Δ) (xs : List (ZMod p))
    (columns : List (UniversalType r Q Δ)) {a b : Data}
    (h : RecordPrograms.Visits (fun _ => false) (effect p i t u xs)
      (columns.map CollisionProgram.encodeType) a b) :
    b.stacks 50 = (rowBytes p i t u xs columns).reverse ++ a.stacks 50 := by
  induction columns generalizing a b with
  | nil =>
      cases h
      simp [rowBytes]
  | cons y ys ih =>
      cases h with
      | hit ht he => contradiction
      | miss ht he history =>
          rw [ih history, he y rfl]
          simp [rowBytes, List.reverse_append, List.append_assoc]

def state (ctx : Fin 46 → List Bool) (regs : Fin 13 → Bool)
    (source accumulator : List Bool) : Data :=
  ⟨regs, fun j => if h : j.val < 46 then ctx ⟨j.val, h⟩
    else if j = 46 then source else if j = 50 then accumulator else []⟩

@[simp] theorem state_low (ctx : Fin 46 → List Bool) (regs : Fin 13 → Bool)
    (source accumulator : List Bool) (j : Fin 46) :
    (state ctx regs source accumulator).stacks (entryPorts j) = ctx j := by
  simp [state, entryPorts, j.isLt]

theorem state_invariant (ctx : Fin 46 → List Bool) (regs : Fin 13 → Bool)
    (source accumulator : List Bool) : invariant ctx (state ctx regs source accumulator) := by
  exact ⟨fun j => state_low ctx regs source accumulator j, rfl, rfl⟩

theorem record_budget (p E : ℕ) (columns : List (UniversalType r Q Δ)) :
    RecordPrograms.budget (callbackCost p E) (columns.map CollisionProgram.encodeType) =
      columns.length * (E + 11 * CollisionProgram.typeWidth r Q Δ + 10 * width p + 24) := by
  induction columns with
  | nil => simp [RecordPrograms.budget]
  | cons y ys ih =>
      simp only [List.map_cons, RecordPrograms.budget, callbackCost,
        CollisionProgram.encodeType_length, ih, List.length_cons]
      ring

def budget (p E count : ℕ) (r Q Δ : ℕ) : ℕ :=
  count * (E + 11 * CollisionProgram.typeWidth r Q Δ + 10 * width p + 24) + 4

theorem program_runsIn (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (i : Fin Δ) (t : Fin Q) (u : UniversalType r Q Δ) (xs : List (ZMod p))
    (columns : List (UniversalType r Q Δ)) (E : ℕ)
    (hE : ∀ y ∈ columns, ConstraintEntryProgram.programBudget p i t u y xs ≤ E)
    (regs : Fin 13 → Bool) (accumulator : List Bool) :
    ∃ out, RunsIn program (budget p E columns.length r Q Δ)
      ((state (context p i t u xs) regs
        (ProgramEncoding.encodeRecords (columns.map CollisionProgram.encodeType)) accumulator).withPC
        (some program.entry))
      ((state (context p i t u xs) out []
        ((rowBytes p i t u xs columns).reverse ++ accumulator)).withPC none) := by
  let ctx := context p i t u xs
  let records := columns.map CollisionProgram.encodeType
  let base := state ctx regs (ProgramEncoding.encodeRecords records) accumulator
  have hv : ∀ bits ∈ records, validPayload p i t u xs E bits := by
    intro bits hb
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
    exact ⟨y, rfl, hE y hy⟩
  obtain ⟨n, next, hn, hi, history, he⟩ := RecordPrograms.iterate_run_with_on
    recordPorts callback (fun _ => false) (callbackCost p E) (invariant ctx)
    (effect p i t u xs) (validPayload p i t u xs E)
    (callback_contract p h2 i t u xs E) records [] base hv
    (state_invariant _ _ _ _) (base.regs 10) (base.regs 11) (base.regs 12)
  have hstart : RecordPrograms.state recordPorts base (base.regs 10) (base.regs 11)
      (base.regs 12) (ProgramEncoding.encodeRecords records ++ []) [] = base := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · change ProgramEncoding.encodeRecords records = ProgramEncoding.encodeRecords records ++ []
      simp only [List.append_nil]
    · rfl
  have hout := visits_output p i t u xs columns history
  let last := RecordPrograms.state recordPorts next false true false [] []
  have hfinish : last = state ctx last.regs []
      ((rowBytes p i t u xs columns).reverse ++ accumulator) := by
    apply congrArg (StructuredProgram.State.mk last.regs)
    funext j
    rcases hi with ⟨hctx, h48, h49⟩
    by_cases hj : j.val < 46
    · have hj46 : j ≠ 46 := by
        intro h; subst j; change 46 < 46 at hj; omega
      have hj47 : j ≠ 47 := by
        intro h; subst j; change 47 < 46 at hj; omega
      have hl := hctx ⟨j.val, hj⟩
      have hid : entryPorts ⟨j.val, hj⟩ = j := Fin.ext rfl
      rw [hid] at hl
      simpa [last, RecordPrograms.state, recordPorts, state, hj, hj46, hj47] using hl
    · have hcases : j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 ∨ j = 50 := by
        have hlt := j.isLt
        simp only [Fin.ext_iff]
        omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl <;>
        simp [recordPorts, state, h48, h49, hout, base]
  have he' : Eval command n base last := by
    have hany : records.any (fun _ => false) = false := by simp only [List.any_eq_false]; simp
    change Eval command n
      (RecordPrograms.state recordPorts base (base.regs 10) (base.regs 11)
        (base.regs 12) (ProgramEncoding.encodeRecords records ++ []) []) _ at he
    rw [hstart] at he
    simpa only [hany, last, TupleProgram.unread_false] using he
  rw [hfinish] at he'
  refine ⟨last.regs, n + 1, ?_, compiled_halt_trace he' 46 50⟩
  change n ≤ 3 + RecordPrograms.budget (callbackCost p E)
    (columns.map CollisionProgram.encodeType) at hn
  rw [record_budget] at hn
  dsimp [budget]
  omega

theorem primitive_runsIn (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (i : Fin Δ) (t : Fin Q) (u : UniversalType r Q Δ) (xs : List (ZMod p))
    (columns : List (UniversalType r Q Δ)) (E : ℕ)
    (hE : ∀ y ∈ columns, ConstraintEntryProgram.programBudget p i t u y xs ≤ E)
    (regs : Fin 13 → Bool) (accumulator : List Bool) :
    ∃ out, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * budget p E columns.length r Q Δ)
      (BitProgram.primitiveCfg program
        ((state (context p i t u xs) regs
          (ProgramEncoding.encodeRecords (columns.map CollisionProgram.encodeType)) accumulator).withPC
          (some program.entry)))
      (BitProgram.primitiveCfg program
        ((state (context p i t u xs) out []
          ((rowBytes p i t u xs columns).reverse ++ accumulator)).withPC none)) := by
  obtain ⟨out, ht⟩ := program_runsIn p h2 i t u xs columns E hE regs accumulator
  exact ⟨out, BitProgram.primitive_execution _ ht⟩

end SubexponentialSAT.Subexp.ConstraintMatrixRow

end OAI.Algorithms
