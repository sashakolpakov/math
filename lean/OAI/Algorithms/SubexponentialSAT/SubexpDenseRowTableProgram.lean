import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-!
# Fixed traversal for the complete dense row table

The input scope stream is the actual factor-order list of encounter-order
scopes. Three fixed loops visit factors, incidences, and ambient coordinates.
The single-row program is linked as executable code; no row list is an input.

This module separates the traversal proof from the still separately proved
packing lookup, incidence-slot query, joint-matrix entry, and row evaluator.
The row service must supply an actual execution on the indicated runtime
inputs before the complete table theorem applies.
-/

namespace SubexponentialSAT.SubexpDenseRowTableProgram

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 25 288
abbrev Code := Cmd 25 288
abbrev Word := List Bool

def unary (n : ℕ) : Word := List.replicate n true

/-- This is the existing numeric scope format, including its natural-number
terminators. It is not a list of precomputed polynomial rows. -/
def scopeCode (scope : List ℕ) : Word := Encoding.encodeList Encoding.encodeNat scope
def scopesCode (scopes : List (List ℕ)) : Word := Encoding.encodeList scopeCode scopes

def coordinateRows (row : ℕ → ℕ → ℕ → Word) (D e v : ℕ) : List Word :=
  (List.range D).map (row e v)

def incidenceRows (row : ℕ → ℕ → ℕ → Word) (D : ℕ) :
    ℕ → List (List ℕ) → List Word
  | _, [] => []
  | e, scope :: scopes =>
      scope.map (fun v => Encoding.encodeList id (coordinateRows row D e v)) ++
        incidenceRows row D (e + 1) scopes

def tableCode (row : ℕ → ℕ → ℕ → Word) (D : ℕ) (scopes : List (List ℕ)) : Word :=
  Encoding.encodeList id (incidenceRows row D 0 scopes)

@[simp] theorem coordinateRows_length (row : ℕ → ℕ → ℕ → Word) (D e v : ℕ) :
    (coordinateRows row D e v).length = D := by
  simp [coordinateRows]

theorem incidenceRows_length (row : ℕ → ℕ → ℕ → Word) (D e : ℕ)
    (scopes : List (List ℕ)) :
    (incidenceRows row D e scopes).length = (scopes.map List.length).sum := by
  induction scopes generalizing e with
  | nil => rfl
  | cons scope scopes ih => simp [incidenceRows, ih]

/-! The lower 256 stacks are the single-row kernel's ABI. Ports 128 through
137 remain its protected source cache. The temporary high bank is consumed
and cleared before the later node loop reuses ports 256 and 265. -/

def factorPorts : RecordPrograms.Ports 25 288 :=
  ⟨16, 17, 18, 257, 258, by decide, by decide, by decide, by decide⟩

def scopePorts : RecordPrograms.Ports 25 288 :=
  ⟨19, 20, 21, 259, 260, by decide, by decide, by decide, by decide⟩

def atom (a : StructuredProgram.Atom 25 288) : Code := .base (.atom a)

def pushConstant (port : Fin 288) (value : Bool) : Code :=
  .seq (atom (.set 0 value)) (atom (.push port 0))

def transfer (source target : Fin 288) : Code :=
  .call (StackRoutines.transferProgram source target (0 : Fin 25) 1)

def copy (source target : Fin 288) : Code :=
  .call (StackRoutines.copyProgram source target 270 (0 : Fin 25) 1)

def clear (port : Fin 288) : Code :=
  .call (StackRoutines.clearProgram port (0 : Fin 25) 1)

def smallRegisters : Fin 3 → Fin 25 := Fin.castAdd 22

theorem smallRegisters_injective : Function.Injective smallRegisters := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 25 => x.val) h

def emitPorts (source target : Fin 288) : Fin 4 → Fin 288 :=
  ![0, 1, target, source]

/-- Consume the reversed payload and prepend one tagged frame. -/
def emit (source target : Fin 288) : Code :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.emitRecordProgram
    smallRegisters (emitPorts source target))

def reversePorts (source target : Fin 288) : Fin 4 → Fin 288 :=
  ![source, 1, target, 269]

def reverseRecords (source target : Fin 288) : Code :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.reverseRecordsProgram
    smallRegisters (reversePorts source target))

def resetScope : Code := .seq (atom (.set 19 false))
  (.seq (atom (.set 20 true)) (atom (.set 21 false)))

def resetFactor : Code := .seq (atom (.set 16 false))
  (.seq (atom (.set 17 true)) (atom (.set 18 false)))

def coordinatePeek : Code := atom (.peek 263 22 24)

def coordinateBody (row : Code) : Code :=
  .seq (atom (.pop 263 22 24))
    (.seq row (.seq (emit 87 266)
      (.seq (pushConstant 262 true) coordinatePeek)))

/-- The coordinate is the length of the true-unary counter on 262. The
remaining dimension on 263 is physically popped once per row. -/
def coordinateLoop (row : Code) : Code := .while 24 (coordinateBody row)

def coordinates (row : Code) : Code :=
  .seq (copy 264 263)
    (.seq (pushConstant 266 false)
      (.seq coordinatePeek (.seq (coordinateLoop row)
        (.seq (clear 262) (.seq (pushConstant 267 false)
          (reverseRecords 266 267))))))

/-- The parser returns `false :: unary v`, the reversed numeric encoding.
The one-bit pop removes that terminator before the row service sees v. -/
def incidenceCallback (row : Code) : Code :=
  .seq (atom (.pop 260 0 1))
    (.seq (coordinates row)
      (.seq (transfer 267 269)
        (.seq (emit 269 268) (.seq (clear 260) resetScope))))

def factorCallback (row : Code) : Code :=
  .seq (transfer 258 259)
    (.seq (RecordPrograms.iterate scopePorts (incidenceCallback row))
      (.seq (pushConstant 261 true) resetFactor))

/-- Inputs: numeric scopes 256, unary dimension 264, computed packing lookup
265, and the prepared source context in the lower bank. Output: table 255.
The row service reads factor/vertex/coordinate counters 261/260/262 and
returns the complete reversed flat row on 87, restoring all other stacks. -/
def command (row : Code) : Code :=
  .seq (copy 256 257)
    (.seq (pushConstant 268 false)
      (.seq (RecordPrograms.iterate factorPorts (factorCallback row))
        (.seq (clear 261) (.seq (clear 256)
          (.seq (clear 264) (.seq (clear 265)
            (.seq (pushConstant 255 false) (reverseRecords 268 255))))))))

abbrev program (row : Code) : Program 25 288 (size (command row) + 1) :=
  compiled (command row) 256 255

def pushed (port : Fin 288) (value : Bool) (a : Data) : Data :=
  ⟨Function.update a.regs 0 value, Function.update a.stacks port (value :: a.stacks port)⟩

theorem pushConstant_eval (port : Fin 288) (value : Bool) (a : Data) :
    Eval (pushConstant port value) 2 a (pushed port value a) := by
  let b : Data := ⟨Function.update a.regs 0 value, a.stacks⟩
  have h₁ : Eval (atom (.set 0 value)) 1 a b := .base (.atom _ _)
  have h₂ : Eval (atom (.push port 0)) 1 b (pushed port value a) := by
    apply Eval.base
    simpa [b, pushed, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using
      StructuredProgram.Eval.atom (StructuredProgram.Atom.push port (0 : Fin 25)) b
  exact h₁.seq h₂

def transferred (source target : Fin 288) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.transferStacks source target a.stacks⟩

theorem transfer_eval (source target : Fin 288) (hne : source ≠ target) (a : Data) :
    Eval (transfer source target) (3 * (a.stacks source).length + 3) a
      (transferred source target a) :=
  .call _ (ListRegisterProgram.transfer_run source target 0 1 hne (by decide) a.regs a.stacks)

def copied (source target : Fin 288) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks source target a.stacks⟩

theorem copy_eval (source target : Fin 288) (hne : source ≠ target)
    (hs : source ≠ 270) (ht : (270 : Fin 288) ≠ target) (a : Data)
    (ha : a.stacks 270 = []) :
    Eval (copy source target) (7 * (a.stacks source).length + 5) a (copied source target a) :=
  .call _ (ListRegisterProgram.copy_run source target 270 0 1 hne hs ht (by decide)
    a.regs a.stacks ha)

def cleared (port : Fin 288) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks port a.stacks⟩

theorem clear_eval (port : Fin 288) (a : Data) :
    Eval (clear port) (2 * (a.stacks port).length + 3) a (cleared port a) :=
  .call _ (ListRegisterProgram.clear_run port 0 1 a.regs a.stacks)

theorem emitPorts_injective (source target : Fin 288)
    (hs0 : source ≠ 0) (hs1 : source ≠ 1) (ht0 : target ≠ 0) (ht1 : target ≠ 1)
    (hne : source ≠ target) : Function.Injective (emitPorts source target) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [emitPorts]

def emitted (source target : Fin 288) (bits : Word) (a : Data) : Data :=
  ⟨Function.update (Function.update a.regs 0 true) 1 false,
    Function.update (Function.update a.stacks source []) target
      (true :: (Encoding.frame bits ++ a.stacks target))⟩

/-- The row writer is an actual finite record-encoding program. Its source
payload is consumed and every other stack except the destination is framed. -/
theorem emit_eval (source target : Fin 288)
    (hs0 : source ≠ 0) (hs1 : source ≠ 1) (ht0 : target ≠ 0) (ht1 : target ≠ 1)
    (hne : source ≠ target) (a : Data) (bits : Word)
    (hbits : a.stacks source = bits.reverse) :
    Eval (emit source target) (5 * bits.length + 7) a (emitted source target bits a) := by
  let s := SubexpNormalizeProgram.filterState (a.regs 0) (a.regs 1) (a.regs 2)
    (a.stacks 0) (a.stacks 1) (a.stacks target) bits.reverse
  let t := SubexpNormalizeProgram.filterState true false (a.regs 2)
    (a.stacks 0) (a.stacks 1) (true :: (Encoding.frame bits ++ a.stacks target)) []
  have hm := emitPorts_injective source target hs0 hs1 ht0 ht1 hne
  have hstart : embedState smallRegisters (emitPorts source target) a s = a := by
    apply embedState_eq_of_ports _ _ _ _ _ smallRegisters_injective hm
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i <;> first | rfl | exact hbits
    · intros; rfl
  have hend : embedState smallRegisters (emitPorts source target) a t =
      emitted source target bits a := by
    apply embedState_eq_of_ports _ _ _ _ _ smallRegisters_injective hm
    · intro i
      fin_cases i <;> simp [smallRegisters, emitted, t, SubexpNormalizeProgram.filterState]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
      simp [emitted, h0, h1]
    · intro i
      fin_cases i <;> simp [emitPorts, emitted, t, SubexpNormalizeProgram.filterState,
        hne, Ne.symm hs0, Ne.symm hs1, Ne.symm ht0, Ne.symm ht1]
    · intro i hi
      have hs : i ≠ source := fun h => hi ⟨3, h.symm⟩
      have ht : i ≠ target := fun h => hi ⟨2, h.symm⟩
      simp [emitted, hs, ht]
  have h := eval_call_lifted SubexpNormalizeProgram.emitRecordProgram
    smallRegisters (emitPorts source target) a smallRegisters_injective hm
    (SubexpNormalizeProgram.emitRecord_trace bits (a.stacks 0) (a.stacks 1)
      (a.stacks target) (a.regs 0) (a.regs 1) (a.regs 2))
  change Eval (emit source target) _
    (embedState smallRegisters (emitPorts source target) a s)
    (embedState smallRegisters (emitPorts source target) a t) at h
  simpa only [hstart, hend] using h

theorem reversePorts_injective (source target : Fin 288)
    (hs1 : source ≠ 1) (hs269 : source ≠ 269) (ht1 : target ≠ 1)
    (ht269 : target ≠ 269) (hne : source ≠ target) :
    Function.Injective (reversePorts source target) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [reversePorts]

def reversedRecords (source target : Fin 288) (records acc : List Word)
    (suffix : Word) (a : Data) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 0 false) 1 true) 2 false,
    Function.update (Function.update a.stacks source suffix) target
      (Encoding.encodeList id (records.reverse ++ acc))⟩

theorem reverseRecords_eval (source target : Fin 288)
    (hs1 : source ≠ 1) (hs269 : source ≠ 269) (ht1 : target ≠ 1)
    (ht269 : target ≠ 269) (hne : source ≠ target)
    (a : Data) (records acc : List Word) (suffix : Word)
    (hsource : a.stacks source = Encoding.encodeList id records ++ suffix)
    (htarget : a.stacks target = Encoding.encodeList id acc)
    (hwork : a.stacks 269 = []) :
    ∃ n ≤ 10 * (Encoding.encodeList id records).length,
      Eval (reverseRecords source target) n a
        (reversedRecords source target records acc suffix a) := by
  let s := SubexpNormalizeProgram.filterState (a.regs 0) (a.regs 1) (a.regs 2)
    (Encoding.encodeList id records ++ suffix) (a.stacks 1)
    (Encoding.encodeList id acc) []
  let t := SubexpNormalizeProgram.filterState false true false suffix (a.stacks 1)
    (Encoding.encodeList id (records.reverse ++ acc)) []
  have hm := reversePorts_injective source target hs1 hs269 ht1 ht269 hne
  have hstart : embedState smallRegisters (reversePorts source target) a s = a := by
    apply embedState_eq_of_ports _ _ _ _ _ smallRegisters_injective hm
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i
      fin_cases i
      · exact hsource
      · rfl
      · exact htarget
      · exact hwork
    · intros; rfl
  have hend : embedState smallRegisters (reversePorts source target) a t =
      reversedRecords source target records acc suffix a := by
    apply embedState_eq_of_ports _ _ _ _ _ smallRegisters_injective hm
    · intro i
      fin_cases i <;> simp [smallRegisters, reversedRecords, t,
        SubexpNormalizeProgram.filterState]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
      have h2 : i ≠ 2 := fun h => hi ⟨2, h.symm⟩
      simp [reversedRecords, h0, h1, h2]
    · intro i
      fin_cases i <;> simp [reversePorts, reversedRecords, t,
        SubexpNormalizeProgram.filterState, hne, Ne.symm hs1, Ne.symm hs269,
        Ne.symm ht1, Ne.symm ht269, hwork]
    · intro i hi
      have hs : i ≠ source := fun h => hi ⟨0, h.symm⟩
      have ht : i ≠ target := fun h => hi ⟨2, h.symm⟩
      simp [reversedRecords, hs, ht]
  obtain ⟨n, hn, hr⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records acc suffix
    (a.stacks 1) (a.regs 0) (a.regs 1) (a.regs 2)
  have h := eval_call_lifted SubexpNormalizeProgram.reverseRecordsProgram
    smallRegisters (reversePorts source target) a smallRegisters_injective hm hr
  change Eval (reverseRecords source target) _
    (embedState smallRegisters (reversePorts source target) a s)
    (embedState smallRegisters (reversePorts source target) a t) at h
  exact ⟨n, hn, by simpa only [hstart, hend] using h⟩

/-! The coordinate loop below uses the literal runtime counters. Its row
contract is an execution of the supplied finite code, with an explicit frame;
it cannot be discharged by a polynomial value or by a cost annotation. -/

def coordinateState (frame : Data) (regs : Fin 25 → Bool)
    (index remaining : ℕ) (records : List Word) (output : Word) : Data :=
  ⟨regs, Function.update
    (Function.update (Function.update (Function.update frame.stacks 87 output)
      262 (unary index)) 263 (unary remaining)) 266 (Encoding.encodeList id records)⟩

@[simp] theorem coordinateState_regs (frame : Data) (regs : Fin 25 → Bool)
    (index remaining : ℕ) (records : List Word) (output : Word) :
    (coordinateState frame regs index remaining records output).regs = regs := rfl

@[simp] theorem coordinateState_output (frame : Data) (regs : Fin 25 → Bool)
    (index remaining : ℕ) (records : List Word) (output : Word) :
    (coordinateState frame regs index remaining records output).stacks 87 = output := by
  simp [coordinateState]

@[simp] theorem coordinateState_index (frame : Data) (regs : Fin 25 → Bool)
    (index remaining : ℕ) (records : List Word) (output : Word) :
    (coordinateState frame regs index remaining records output).stacks 262 = unary index := by
  simp [coordinateState]

@[simp] theorem coordinateState_remaining (frame : Data) (regs : Fin 25 → Bool)
    (index remaining : ℕ) (records : List Word) (output : Word) :
    (coordinateState frame regs index remaining records output).stacks 263 = unary remaining := by
  simp [coordinateState]

@[simp] theorem coordinateState_records (frame : Data) (regs : Fin 25 → Bool)
    (index remaining : ℕ) (records : List Word) (output : Word) :
    (coordinateState frame regs index remaining records output).stacks 266 =
      Encoding.encodeList id records := by simp [coordinateState]

theorem coordinateState_frame (frame : Data) (regs : Fin 25 → Bool)
    (index remaining : ℕ) (records : List Word) (output : Word) (i : Fin 288)
    (h87 : i ≠ 87) (h262 : i ≠ 262) (h263 : i ≠ 263) (h266 : i ≠ 266) :
    (coordinateState frame regs index remaining records output).stacks i = frame.stacks i := by
  simp [coordinateState, h87, h262, h263, h266]

def peekRegs (regs : Fin 25 → Bool) (remaining : ℕ) : Fin 25 → Bool :=
  readRegs regs 22 24 (unary remaining).head?

@[simp] theorem peekRegs_zero (regs : Fin 25 → Bool) : peekRegs regs 0 24 = false := by
  simp [peekRegs, unary]

@[simp] theorem peekRegs_succ (regs : Fin 25 → Bool) (remaining : ℕ) :
    peekRegs regs (remaining + 1) 24 = true := by
  simp [peekRegs, unary, List.replicate_succ]

theorem coordinatePeek_eval (frame : Data) (regs : Fin 25 → Bool)
    (index remaining : ℕ) (records : List Word) (output : Word) :
    Eval coordinatePeek 1 (coordinateState frame regs index remaining records output)
      (coordinateState frame (peekRegs regs remaining) index remaining records output) := by
  simpa [coordinatePeek, atom, coordinateState, peekRegs, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using
    Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.peek 263 22 24)
      (coordinateState frame regs index remaining records output))

theorem coordinatePop_eval (frame : Data) (regs : Fin 25 → Bool)
    (index remaining : ℕ) (records : List Word) :
    Eval (atom (.pop 263 22 24)) 1
      (coordinateState frame regs index (remaining + 1) records [])
      (coordinateState frame (readRegs regs 22 24 (some true)) index remaining records []) := by
  have h := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.pop 263 22 24)
    (coordinateState frame regs index (remaining + 1) records []))
  convert h using 1
  · rfl
  · apply congrArg₂ StructuredProgram.State.mk
    · simp [coordinateState, unary, List.replicate_succ, StructuredProgram.Atom.instr,
        execInstr]
    · funext i
      by_cases hi : i = 263 <;>
        simp [coordinateState, unary, List.replicate_succ, StructuredProgram.Atom.instr,
          execInstr, Function.update_apply, hi]

theorem coordinateEmit_eval (frame : Data) (regs : Fin 25 → Bool)
    (index remaining : ℕ) (records : List Word) (bits : Word) :
    Eval (emit 87 266) (5 * bits.length + 7)
      (coordinateState frame regs index remaining records bits.reverse)
      (coordinateState frame (Function.update (Function.update regs 0 true) 1 false)
        index remaining (bits :: records) []) := by
  have h := emit_eval 87 266 (by decide) (by decide) (by decide) (by decide) (by decide)
    (coordinateState frame regs index remaining records bits.reverse) bits (by simp)
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    by_cases h87 : i = 87 <;> by_cases h266 : i = 266 <;>
      simp [coordinateState, Encoding.encodeList, h87, h266,
        Function.update_apply]

theorem coordinateIncrement_eval (frame : Data) (regs : Fin 25 → Bool)
    (index remaining : ℕ) (records : List Word) :
    Eval (pushConstant 262 true) 2
      (coordinateState frame regs index remaining records [])
      (coordinateState frame (Function.update regs 0 true) (index + 1) remaining records []) := by
  have h := pushConstant_eval 262 true (coordinateState frame regs index remaining records [])
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    by_cases hi : i = 262 <;>
      simp [coordinateState, unary, List.replicate_succ,
        Function.update_apply, hi]

/-- A fixed row body runs on a runtime coordinate and returns its complete
reversed coefficient array. Every stack outside its output is restored. The
contract is restricted to the finite coordinate interval actually visited. -/
def RowContract (row : Code) (render : ℕ → Word) (cost : ℕ → ℕ)
    (frame : Data) (D : ℕ) : Prop :=
  ∀ (index : ℕ), index < D → ∀ (remaining : ℕ) (records : List Word)
    (regs : Fin 25 → Bool),
    ∃ n ≤ cost index, ∃ nextRegs,
      Eval row n (coordinateState frame regs index remaining records [])
        (coordinateState frame nextRegs index remaining records (render index).reverse)

def coordinateBudget (render : ℕ → Word) (cost : ℕ → ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 1
  | index, remaining + 1 =>
      cost index + 5 * (render index).length + 12 +
        coordinateBudget render cost (index + 1) remaining

def collectedRows (render : ℕ → Word) : ℕ → ℕ → List Word → List Word
  | _, 0, records => records
  | index, remaining + 1, records =>
      collectedRows render (index + 1) remaining (render index :: records)

/-- Exact ascending-coordinate traversal of the physical unary counter.
The accumulator contains complete rows in reverse encounter order, ready
for the subsequent actual record reversal. -/
theorem coordinateLoop_eval (row : Code) (render : ℕ → Word) (cost : ℕ → ℕ)
    (frame : Data) (D : ℕ) (hrow : RowContract row render cost frame D)
    (index remaining : ℕ) (hlimit : index + remaining ≤ D)
    (records : List Word) (regs : Fin 25 → Bool) :
    ∃ n ≤ coordinateBudget render cost index remaining, ∃ nextRegs,
      Eval (coordinateLoop row) n
        (coordinateState frame (peekRegs regs remaining) index remaining records [])
        (coordinateState frame nextRegs (index + remaining) 0
          (collectedRows render index remaining records) []) := by
  induction remaining generalizing index records regs with
  | zero =>
      refine ⟨1, le_rfl, peekRegs regs 0, ?_⟩
      simpa [coordinateLoop, collectedRows] using
        Eval.while_false (body := coordinateBody row)
          (a := coordinateState frame (peekRegs regs 0) index 0 records []) (by simp)
  | succ remaining ih =>
      let initialRegs := peekRegs regs (remaining + 1)
      let poppedRegs := readRegs initialRegs 22 24 (some true)
      obtain ⟨n, hn, rowRegs, hr⟩ := hrow index (by omega) remaining records poppedRegs
      let emittedRegs := Function.update (Function.update rowRegs 0 true) 1 false
      let nextRegs := Function.update emittedRegs 0 true
      have hp := coordinatePop_eval frame initialRegs index remaining records
      have he := coordinateEmit_eval frame rowRegs index remaining records (render index)
      have hi := coordinateIncrement_eval frame emittedRegs index remaining
        (render index :: records)
      have hk := coordinatePeek_eval frame nextRegs (index + 1) remaining
        (render index :: records) []
      have hb := hp.seq (hr.seq (he.seq (hi.seq hk)))
      obtain ⟨m, hm, finalRegs, htail⟩ := ih (index + 1) (by omega)
        (render index :: records) nextRegs
      have run := Eval.while_true (body := coordinateBody row)
        (by simp [initialRegs]) hb htail
      refine ⟨1 + (n + ((5 * (render index).length + 7) + (2 + 1))) + m + 1,
        ?_, finalRegs, ?_⟩
      · simp only [coordinateBudget]
        omega
      · simpa [coordinateLoop, coordinateBody, collectedRows, initialRegs,
          poppedRegs, emittedRegs, nextRegs, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using run

theorem collectedRows_eq (render : ℕ → Word) (index remaining : ℕ)
    (records : List Word) :
    collectedRows render index remaining records =
      ((List.range' index remaining).map render).reverse ++ records := by
  induction remaining generalizing index records with
  | zero => simp [collectedRows]
  | succ remaining ih =>
      simp [collectedRows, ih, List.range'_succ, List.reverse_cons, List.append_assoc]

theorem coordinateBudget_le (render : ℕ → Word) (cost : ℕ → ℕ)
    (index remaining C B : ℕ)
    (hc : ∀ i, index ≤ i → i < index + remaining → cost i ≤ C)
    (hb : ∀ i, index ≤ i → i < index + remaining → (render i).length ≤ B) :
    coordinateBudget render cost index remaining ≤ remaining * (C + 5 * B + 12) + 1 := by
  induction remaining generalizing index with
  | zero => simp [coordinateBudget]
  | succ remaining ih =>
      have hi := ih (index + 1) (fun i hi hj => hc i (by omega) (by omega))
        (fun i hi hj => hb i (by omega) (by omega))
      have hci := hc index (by omega) (by omega)
      have hbi := hb index (by omega) (by omega)
      simp only [coordinateBudget]
      nlinarith

end SubexponentialSAT.SubexpDenseRowTableProgram

end OAI.Algorithms
