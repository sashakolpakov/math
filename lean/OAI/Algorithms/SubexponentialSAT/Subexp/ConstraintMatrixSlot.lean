import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintMatrixRowExecution

namespace OAI.Algorithms

/-! Emit every row from one actual Joint list. The saved Side list is copied
for each row; a unary counter records the number of emitted matrix rows. -/

namespace SubexponentialSAT.Subexp.ConstraintMatrixSlot

open BitProgram StructuredCalls StackRoutines MatrixWordEncoding MulticolorTypes

abbrev Data := State 16 56

def rowRegisters : Fin 13 → Fin 16 := Fin.castAdd 3
def rowPorts : Fin 51 → Fin 56 := Fin.castAdd 5

theorem rowRegisters_injective : Function.Injective rowRegisters := Fin.castAdd_injective _ _
theorem rowPorts_injective : Function.Injective rowPorts := Fin.castAdd_injective _ _
theorem rowPorts_ne (j : Fin 51) (k : Fin 56) (hk : 51 ≤ k.val) : rowPorts j ≠ k := by
  intro h
  have hv : j.val = k.val := congrArg Fin.val h
  have hj := j.isLt
  omega

def recordPorts : RecordPrograms.Ports 16 56 :=
  ⟨13, 14, 15, 51, 52, by decide, by decide, by decide, by decide⟩

abbrev row : Cmd 16 56 := .call
  (ProgramLinking.liftProgram ConstraintMatrixRow.program rowRegisters rowPorts)
abbrev callback : Cmd 16 56 := .seq (.call (transferProgram 52 23 0 1))
  (.seq (.call (copyProgram 53 46 54 0 1))
    (.seq row (.seq (.call (clearProgram 23 0 1)) (TupleProgram.pushConst 55 0 true))))
abbrev command : Cmd 16 56 := RecordPrograms.iterate recordPorts callback
def program := compiled command 51 50

noncomputable def afterRow (a : Data) (regs : Fin 13 → Bool) (rowBytes : List Bool) : Data :=
  ⟨Function.extend rowRegisters regs a.regs,
    Function.update (Function.update a.stacks 46 []) 50 (rowBytes.reverse ++ a.stacks 50)⟩

theorem afterRow_register_frame (a : Data) (regs : Fin 13 → Bool) (bytes : List Bool)
    (j : Fin 16) (hj : 13 ≤ j.val) : (afterRow a regs bytes).regs j = a.regs j := by
  apply Function.extend_apply'
  rintro ⟨k, hk⟩
  have hv : k.val = j.val := congrArg Fin.val hk
  have hlt := k.isLt
  omega

variable {r Q Δ : ℕ}

def context (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q)
    (anchor : UniversalType r Q Δ) (xs : List (ZMod p)) : Fin 51 → List Bool :=
  Function.update
    (ConstraintMatrixRow.state (ConstraintMatrixRow.context p i t anchor xs)
      (fun _ => false) [] []).stacks 23 []

theorem context_row (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q)
    (anchor u : UniversalType r Q Δ) (xs : List (ZMod p)) (j : Fin 46) :
    (Function.update (context p i t anchor xs) 23 (CollisionProgram.encodeType u))
      (ConstraintMatrixRow.entryPorts j) = ConstraintMatrixRow.context p i t u xs j := by
  fin_cases j <;> rfl

@[simp] theorem context_23 (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q)
    (anchor : UniversalType r Q Δ) (xs : List (ZMod p)) : context p i t anchor xs 23 = [] := by
  simp [context]

@[simp] theorem context_high (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q)
    (anchor : UniversalType r Q Δ) (xs : List (ZMod p)) (j : Fin 51) (hj : 46 ≤ j.val) :
    context p i t anchor xs j = [] := by
  have hn : ¬ j.val < 46 := by omega
  have h23 : j ≠ 23 := by
    intro h; subst j; change 46 ≤ 23 at hj; omega
  simp [context, ConstraintMatrixRow.state, hn, h23]

theorem row_eval (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (i : Fin Δ) (t : Fin Q) (u : UniversalType r Q Δ) (xs : List (ZMod p))
    (columns : List (UniversalType r Q Δ)) (E : ℕ)
    (hE : ∀ y ∈ columns, ConstraintEntryProgram.programBudget p i t u y xs ≤ E)
    (a : Data)
    (ha : projectState rowRegisters rowPorts a =
      ConstraintMatrixRow.state (ConstraintMatrixRow.context p i t u xs)
        (a.regs ∘ rowRegisters)
        (ProgramEncoding.encodeRecords (columns.map CollisionProgram.encodeType)) (a.stacks 50)) :
    ∃ n ≤ ConstraintMatrixRow.budget p E columns.length r Q Δ, ∃ out,
      Eval row n a (afterRow a out (ConstraintMatrixRow.rowBytes p i t u xs columns)) := by
  let bytes := ConstraintMatrixRow.rowBytes p i t u xs columns
  obtain ⟨out, n, hn, ht⟩ := ConstraintMatrixRow.program_runsIn p h2 i t u xs columns E hE
    (a.regs ∘ rowRegisters) (a.stacks 50)
  have ht' : Trace ConstraintMatrixRow.program n
      ((projectState rowRegisters rowPorts a).withPC (some ConstraintMatrixRow.program.entry))
      ((ConstraintMatrixRow.state (ConstraintMatrixRow.context p i t u xs) out []
        (bytes.reverse ++ a.stacks 50)).withPC none) := by simpa only [ha] using ht
  have he := eval_call_from_state ConstraintMatrixRow.program rowRegisters rowPorts a
    rowRegisters_injective rowPorts_injective ht'
  have hb : Function.extend rowPorts (projectState rowRegisters rowPorts a).stacks a.stacks =
      a.stacks := congrArg StructuredProgram.State.stacks
        (embedState_project rowRegisters rowPorts a rowRegisters_injective rowPorts_injective)
  have hl : (ConstraintMatrixRow.state (ConstraintMatrixRow.context p i t u xs) out []
        (bytes.reverse ++ a.stacks 50)).stacks =
      Function.update (Function.update (projectState rowRegisters rowPorts a).stacks 46 [])
        50 (bytes.reverse ++ a.stacks 50) := by
    rw [ha]
    funext j
    fin_cases j <;> rfl
  have hend : embedState rowRegisters rowPorts a
      (ConstraintMatrixRow.state (ConstraintMatrixRow.context p i t u xs) out []
        (bytes.reverse ++ a.stacks 50)) = afterRow a out bytes := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · rw [hl, ProgramLinking.extend_update rowPorts_injective,
        ProgramLinking.extend_update rowPorts_injective, hb]
      rfl
  exact ⟨n, hn, out, hend ▸ he⟩

def invariant (ctx : Fin 51 → List Bool) (columns : List Bool) (a : Data) : Prop :=
  (∀ j, j ≠ 50 → a.stacks (rowPorts j) = ctx j) ∧ a.stacks 53 = columns ∧ a.stacks 54 = []

def callbackCost (p E N columnBytes r Q Δ : ℕ) (bits : List Bool) : ℕ :=
  ConstraintMatrixRow.budget p E N r Q Δ + 5 * bits.length + 7 * columnBytes + 13

def effect (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q) (xs : List (ZMod p))
    (columns : List (UniversalType r Q Δ)) (bits : List Bool) (a b : Data) : Prop :=
  (∀ u : UniversalType r Q Δ, CollisionProgram.encodeType u = bits →
    b.stacks 50 = (ConstraintMatrixRow.rowBytes p i t u xs columns).reverse ++ a.stacks 50) ∧
    b.stacks 55 = true :: a.stacks 55

def validPayload (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q) (xs : List (ZMod p))
    (columns : List (UniversalType r Q Δ)) (E : ℕ) (bits : List Bool) : Prop :=
  ∃ u : UniversalType r Q Δ, bits = CollisionProgram.encodeType u ∧
    ∀ y ∈ columns, ConstraintEntryProgram.programBudget p i t u y xs ≤ E

theorem filled_context (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q)
    (anchor u : UniversalType r Q Δ) (xs : List (ZMod p)) :
    Function.update (context p i t anchor xs) 23 (CollisionProgram.encodeType u) =
      (ConstraintMatrixRow.state (ConstraintMatrixRow.context p i t u xs)
        (fun _ => false) [] []).stacks := by
  funext j
  by_cases hj : j.val < 46
  · have hid : ConstraintMatrixRow.entryPorts ⟨j.val, hj⟩ = j := Fin.ext rfl
    have h := context_row p i t anchor u xs ⟨j.val, hj⟩
    rw [hid] at h
    simpa [ConstraintMatrixRow.state, hj] using h
  · have hj23 : j ≠ 23 := by
      intro h; subst j; change ¬ 23 < 46 at hj; omega
    simp [Function.update_of_ne hj23, context_high p i t anchor xs j (by omega),
      ConstraintMatrixRow.state, hj]

theorem callback_contract (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (i : Fin Δ) (t : Fin Q) (anchor : UniversalType r Q Δ) (xs : List (ZMod p))
    (columns : List (UniversalType r Q Δ)) (E : ℕ) :
    RecordPrograms.CallbackContractWithOn recordPorts callback (fun _ => false)
      (callbackCost p E columns.length
        (ProgramEncoding.encodeRecords (columns.map CollisionProgram.encodeType)).length r Q Δ)
      (invariant (context p i t anchor xs)
        (ProgramEncoding.encodeRecords (columns.map CollisionProgram.encodeType)))
      (effect p i t xs columns) (validPayload p i t xs columns E) := by
  intro bits tail base hv hi
  obtain ⟨u, rfl, hE⟩ := hv
  rcases hi with ⟨hctx, h53, h54⟩
  let bits := CollisionProgram.encodeType u
  let colBytes := ProgramEncoding.encodeRecords (columns.map CollisionProgram.encodeType)
  let bytes := ConstraintMatrixRow.rowBytes p i t u xs columns
  let a := RecordPrograms.state recordPorts base false true false tail bits.reverse
  let b : Data := ⟨readRegs a.regs 0 1 none, transferStacks 52 23 a.stacks⟩
  let c : Data := ⟨readRegs b.regs 0 1 none, copyStacks 53 46 b.stacks⟩
  have ha23 : a.stacks 23 = [] := by
    simpa [a, recordPorts, RecordPrograms.state, rowPorts] using hctx 23 (by decide)
  have ha46 : a.stacks 46 = [] := by
    simpa [a, recordPorts, RecordPrograms.state, rowPorts] using hctx 46 (by decide)
  have ha52 : a.stacks 52 = bits.reverse := by simp [a, recordPorts, RecordPrograms.state]
  have ha53 : a.stacks 53 = colBytes := by simpa [a, recordPorts, RecordPrograms.state] using h53
  have hc53 : c.stacks 53 = colBytes := by simp [c, copyStacks, b, transferStacks, ha53]
  have hcProjection : (projectState rowRegisters rowPorts c).stacks =
      Function.update
        (Function.update (Function.update (context p i t anchor xs) 23 bits) 46 colBytes)
        50 (c.stacks 50) := by
    funext j
    by_cases hj23 : j = 23
    · subst j
      simp [projectState, rowPorts, c, copyStacks, b, transferStacks, ha23, ha52]
    by_cases hj46 : j = 46
    · subst j
      simp [projectState, rowPorts, c, copyStacks, b, transferStacks, ha46, ha53]
    by_cases hj50 : j = 50
    · subst j; simp [projectState, rowPorts]
    have hn51 := rowPorts_ne j 51 (by decide)
    have hn52 := rowPorts_ne j 52 (by decide)
    have hn23 : rowPorts j ≠ 23 := fun h =>
      hj23 (Fin.ext (congrArg (fun k : Fin 56 => k.val) h))
    have hn46 : rowPorts j ≠ 46 := fun h =>
      hj46 (Fin.ext (congrArg (fun k : Fin 56 => k.val) h))
    simp [projectState, c, copyStacks, b, transferStacks, a, recordPorts,
      RecordPrograms.state, hn51, hn52, hn23, hn46, hj23, hj46, hj50, hctx j hj50]
  have hc : projectState rowRegisters rowPorts c =
      ConstraintMatrixRow.state (ConstraintMatrixRow.context p i t u xs)
        (c.regs ∘ rowRegisters) colBytes (c.stacks 50) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · change (projectState rowRegisters rowPorts c).stacks =
        (ConstraintMatrixRow.state (ConstraintMatrixRow.context p i t u xs)
          (c.regs ∘ rowRegisters) colBytes (c.stacks 50)).stacks
      rw [hcProjection, filled_context]
      funext j
      fin_cases j <;> rfl
  have t0 := TupleProgram.transfer_eval (52 : Fin 56) 23 (0 : Fin 16) 1
    (by decide) (by decide) a
  have t1 := TupleProgram.copy_eval (53 : Fin 56) 46 54 (0 : Fin 16) 1
    (by decide) (by decide) (by decide) (by decide) b
    (by simp [b, transferStacks, a, recordPorts, RecordPrograms.state, h54])
  obtain ⟨nr, hnr, rr, tr⟩ := row_eval p h2 i t u xs columns E hE c hc
  let d := afterRow c rr bytes
  let e : Data := ⟨readRegs d.regs 0 1 none, clearStacks 23 d.stacks⟩
  let f := TupleProgram.pushedState 55 0 true e
  have td := TupleProgram.clear_eval (23 : Fin 56) (0 : Fin 16) 1 d
  have te := TupleProgram.pushConst_eval (55 : Fin 56) (0 : Fin 16) true e
  have hd23 : d.stacks 23 = bits := by
    simp [d, afterRow, c, copyStacks, b, transferStacks, ha23, ha52]
  have hb53 : b.stacks 53 = colBytes := by simp [b, transferStacks, ha53]
  have hfstack : f.stacks =
      Function.update (Function.update (Function.update a.stacks 52 [])
        50 (bytes.reverse ++ a.stacks 50)) 55 (true :: a.stacks 55) := by
    funext j
    by_cases hj23 : j = 23
    · subst j; simp [f, e, clearStacks, ha23]
    by_cases hj46 : j = 46
    · subst j
      simp [f, e, clearStacks, d, afterRow, ha46]
    by_cases hj50 : j = 50
    · subst j
      simp [f, e, clearStacks, d, afterRow,
        c, copyStacks, b, transferStacks]
    by_cases hj52 : j = 52
    · subst j
      simp [f, e, clearStacks, d, afterRow,
        c, copyStacks, b, transferStacks]
    by_cases hj55 : j = 55
    · subst j
      simp [f, e, clearStacks, d, afterRow,
        c, copyStacks, b, transferStacks]
    simp [f, e, clearStacks, d, afterRow,
      c, copyStacks, b, transferStacks, hj23, hj46, hj50, hj52, hj55]
  have hfreg (j : Fin 16) (hj : 13 ≤ j.val) : f.regs j = a.regs j := by
    have hj0 : j ≠ 0 := by intro h; subst j; norm_num at hj
    have hj1 : j ≠ 1 := by intro h; subst j; norm_num at hj
    simp only [f, e, readRegs,
      Function.update_of_ne hj0, Function.update_of_ne hj1]
    rw [afterRow_register_frame c rr bytes j hj]
    simp [c, b, readRegs, hj0, hj1]
  have hfs : RecordPrograms.state recordPorts f false true false tail [] = f := by
    apply RecordPrograms.state_eq_self
    · simpa [recordPorts, a, RecordPrograms.state] using hfreg 13 (by decide)
    · simpa [recordPorts, a, RecordPrograms.state] using hfreg 14 (by decide)
    · simpa [recordPorts, a, RecordPrograms.state] using hfreg 15 (by decide)
    · simp [recordPorts, hfstack, a, RecordPrograms.state]
    · simp [recordPorts, hfstack]
  have hfi : invariant (context p i t anchor xs) colBytes f := by
    refine ⟨?_, ?_, ?_⟩
    · intro j hj50
      have hn51 := rowPorts_ne j 51 (by decide)
      have hn52 := rowPorts_ne j 52 (by decide)
      have hn55 := rowPorts_ne j 55 (by decide)
      have hn50 : rowPorts j ≠ 50 := fun h =>
        hj50 (Fin.ext (congrArg (fun k : Fin 56 => k.val) h))
      simp [hfstack, a, recordPorts, RecordPrograms.state, hn51, hn52, hn55, hn50, hctx j hj50]
    · simp [hfstack, a, recordPorts, RecordPrograms.state, h53, colBytes]
    · simp [hfstack, a, recordPorts, RecordPrograms.state, h54]
  have hfe : effect p i t xs columns bits base f := by
    refine ⟨?_, ?_⟩
    · intro v hv
      have hvu : v = u := CollisionProgram.encodeType_injective hv
      subst v
      simp [hfstack, a, recordPorts, RecordPrograms.state, bytes]
    · simp [hfstack, a, recordPorts, RecordPrograms.state]
  have hrun := t0.seq (t1.seq (tr.seq (td.seq te)))
  refine ⟨3 * (a.stacks 52).length + 3 +
    (7 * (b.stacks 53).length + 5 + (nr + (2 * (d.stacks 23).length + 3 + 2))),
    f, ?_, hfi, hfe, ?_⟩
  · rw [ha52, hb53, hd23, List.length_reverse]
    dsimp [callbackCost, colBytes, bits]
    omega
  · rw [hfs]
    exact hrun

end SubexponentialSAT.Subexp.ConstraintMatrixSlot

end OAI.Algorithms
