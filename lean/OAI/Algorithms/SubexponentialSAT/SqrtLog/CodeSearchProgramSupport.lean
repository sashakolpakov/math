import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramEnumeration
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCodeBasic

namespace OAI.Algorithms

/-! A fixed eight-label program counts nonzero two-bit cells. The input is
consumed and the count is emitted in unary. This is an actual support counter,
not a unit-cost application of `List.countP`. -/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

open SubexponentialSAT.BitProgram
open scoped BigOperators

abbrev cellStream : List (Bool × Bool) → List Bool
  | [] => []
  | (a,b) :: xs => a :: b :: cellStream xs

abbrev cellWeight : List (Bool × Bool) → ℕ
  | [] => 0
  | (a,b) :: xs => cellWeight xs + (if a || b then 1 else 0)

abbrev cellCost : List (Bool × Bool) → ℕ
  | [] => 3
  | (a,b) :: xs => (if a || b then 7 else 5) + cellCost xs

abbrev supportProgram : Program 4 2 8 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.pop 0 0 1 1, .branch 1 2 7, .pop 0 2 1 3,
    .bor 0 0 2 4, .branch 0 5 0, .set 3 true 6, .push 1 3 0, .halt]

def supportCfg (pc : Option (Fin 8)) (regs : Fin 4 → Bool)
    (input output : List Bool) : Cfg 4 2 8 :=
  ⟨pc, regs, ![input, output]⟩

def supportRoundRegs (regs : Fin 4 → Bool) (a b : Bool) : Fin 4 → Bool :=
  let r := readRegs (readRegs regs 0 1 (some a)) 2 1 (some b)
  let r := Function.update r 0 (a || b)
  if a || b then Function.update r 3 true else r

theorem support_round (regs : Fin 4 → Bool) (a b : Bool)
    (input output : List Bool) :
    Trace supportProgram (if a || b then 7 else 5)
      (supportCfg (some 0) regs (a :: b :: input) output)
      (supportCfg (some 0) (supportRoundRegs regs a b) input
        ((if a || b then [true] else []) ++ output)) := by
  cases a <;> cases b <;>
    apply Computation.Trace.of_iterate <;>
    simp [Function.iterate_succ_apply, step, supportProgram, supportCfg,
      supportRoundRegs, execInstr, readRegs, Function.update_apply] <;>
    funext i <;> fin_cases i <;> simp

theorem support_exit (regs : Fin 4 → Bool) (output : List Bool) :
    Trace supportProgram 3
      (supportCfg (some 0) regs [] output)
      (supportCfg none (readRegs regs 0 1 none) [] output) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, supportProgram, supportCfg,
    execInstr, readRegs, Function.update_apply]

theorem support_trace (xs : List (Bool × Bool)) (regs : Fin 4 → Bool)
    (output : List Bool) :
    ∃ finalRegs, Trace supportProgram (cellCost xs)
      (supportCfg (some 0) regs (cellStream xs) output)
      (supportCfg none finalRegs []
        (List.replicate (cellWeight xs) true ++ output)) := by
  induction xs generalizing regs output with
  | nil => exact ⟨readRegs regs 0 1 none, support_exit regs output⟩
  | cons x xs ih =>
      rcases x with ⟨a,b⟩
      obtain ⟨rf, ht⟩ := ih (supportRoundRegs regs a b)
        ((if a || b then [true] else []) ++ output)
      refine ⟨rf, ?_⟩
      have h := (support_round regs a b (cellStream xs) output).trans ht
      cases a <;> cases b <;>
        simpa [cellCost, cellStream, cellWeight, List.replicate_add,
          List.append_assoc] using h

theorem cellCost_le (xs : List (Bool × Bool)) :
    cellCost xs ≤ 7 * xs.length + 3 := by
  induction xs with
  | nil => simp [cellCost]
  | cons x xs ih =>
      rcases x with ⟨a,b⟩
      cases a <;> cases b <;> simp [cellCost] <;> omega

def ternaryCell (x : SparseCode.F3) : Bool × Bool :=
  (decide (x = 1), decide (x = 2))

theorem ternaryCell_nonzero (x : SparseCode.F3) :
    ((ternaryCell x).1 || (ternaryCell x).2) = decide (x ≠ 0) := by
  fin_cases x <;> decide

theorem ternaryCell_encoding (x : SparseCode.F3) :
    [(ternaryCell x).1, (ternaryCell x).2] =
      SubexpEnumerationPayload.scalarBits x := by
  have hw : SubexpEnumerationPayload.scalarWidth 3 = 2 := by
    norm_num [SubexpEnumerationPayload.scalarWidth]
  unfold SubexpEnumerationPayload.scalarBits
  rw [hw]
  fin_cases x <;> decide

theorem cellStream_ternary (xs : List SparseCode.F3) :
    cellStream (xs.map ternaryCell) =
      StackEncoding.encodeDataStack (SubexpEnumerationPayload.scalarCode 3) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change [(ternaryCell x).1, (ternaryCell x).2] ++ cellStream (xs.map ternaryCell) = _
      rw [ih, ternaryCell_encoding]
      rfl

theorem cellWeight_ternary (xs : List SparseCode.F3) :
    cellWeight (xs.map ternaryCell) =
      (xs.map fun x => if x ≠ 0 then 1 else 0).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, cellWeight, ternaryCell_nonzero,
        decide_eq_true_eq, List.sum_cons, ih]
      omega

theorem support_trace_ternary {D : ℕ} (x : Fin D → SparseCode.F3)
    (regs : Fin 4 → Bool) :
    ∃ rf, RunsIn supportProgram (7 * D + 3)
      (supportCfg (some 0) regs
        (SubexpTupleRefinement.encodeTuple (SubexpEnumerationPayload.scalarCode 3) x) [])
      (supportCfg none rf [] (List.replicate (SparseCode.weight x) true)) := by
  obtain ⟨rf, ht⟩ := support_trace ((List.ofFn x).map ternaryCell) regs []
  refine ⟨rf, cellCost ((List.ofFn x).map ternaryCell), ?_, ?_⟩
  · simpa using cellCost_le ((List.ofFn x).map ternaryCell)
  · have hw : cellWeight ((List.ofFn x).map ternaryCell) = SparseCode.weight x := by
      rw [cellWeight_ternary, List.map_ofFn, List.sum_ofFn, SparseCode.weight_eq_sum]
      rfl
    rw [cellStream_ternary, hw, List.append_nil] at ht
    exact ht

/-- The same operation on the five-bit scalar frames emitted by the audited
modular matrix program. Frame markers are physically consumed. -/
abbrev framedCellStream : List (Bool × Bool) → List Bool
  | [] => []
  | (a,b) :: xs => true :: a :: true :: b :: false :: framedCellStream xs

abbrev framedCellCost : List (Bool × Bool) → ℕ
  | [] => 3
  | (a,b) :: xs => (if a || b then 10 else 8) + framedCellCost xs

abbrev framedSupportProgram : Program 4 2 11 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.pop 0 2 1 1, .branch 1 2 10, .pop 0 0 1 3,
    .pop 0 2 1 4, .pop 0 2 1 5, .pop 0 3 1 6,
    .bor 0 0 2 7, .branch 0 8 0, .set 3 true 9, .push 1 3 0, .halt]

def framedSupportCfg (pc : Option (Fin 11)) (regs : Fin 4 → Bool)
    (input output : List Bool) : Cfg 4 2 11 :=
  ⟨pc, regs, ![input, output]⟩

def framedSupportRoundRegs (regs : Fin 4 → Bool) (a b : Bool) : Fin 4 → Bool :=
  let r := readRegs (readRegs (readRegs (readRegs (readRegs regs
    2 1 (some true)) 0 1 (some a)) 2 1 (some true)) 2 1 (some b)) 3 1 (some false)
  let r := Function.update r 0 (a || b)
  if a || b then Function.update r 3 true else r

theorem framedSupport_round (regs : Fin 4 → Bool) (a b : Bool)
    (input output : List Bool) :
    Trace framedSupportProgram (if a || b then 10 else 8)
      (framedSupportCfg (some 0) regs (true :: a :: true :: b :: false :: input) output)
      (framedSupportCfg (some 0) (framedSupportRoundRegs regs a b) input
        ((if a || b then [true] else []) ++ output)) := by
  cases a <;> cases b <;>
    apply Computation.Trace.of_iterate <;>
    simp [Function.iterate_succ_apply, step, framedSupportProgram, framedSupportCfg,
      framedSupportRoundRegs, execInstr, readRegs, Function.update_apply] <;>
    funext i <;> fin_cases i <;> simp

theorem framedSupport_exit (regs : Fin 4 → Bool) (output : List Bool) :
    Trace framedSupportProgram 3
      (framedSupportCfg (some 0) regs [] output)
      (framedSupportCfg none (readRegs regs 2 1 none) [] output) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, framedSupportProgram, framedSupportCfg,
    execInstr, readRegs, Function.update_apply]

theorem framedSupport_trace (xs : List (Bool × Bool)) (regs : Fin 4 → Bool)
    (output : List Bool) :
    ∃ rf, Trace framedSupportProgram (framedCellCost xs)
      (framedSupportCfg (some 0) regs (framedCellStream xs) output)
      (framedSupportCfg none rf [] (List.replicate (cellWeight xs) true ++ output)) := by
  induction xs generalizing regs output with
  | nil => exact ⟨readRegs regs 2 1 none, framedSupport_exit regs output⟩
  | cons x xs ih =>
      rcases x with ⟨a,b⟩
      obtain ⟨rf, ht⟩ := ih (framedSupportRoundRegs regs a b)
        ((if a || b then [true] else []) ++ output)
      refine ⟨rf, ?_⟩
      have h := (framedSupport_round regs a b (framedCellStream xs) output).trans ht
      cases a <;> cases b <;>
        simpa [framedCellCost, framedCellStream, cellWeight, List.replicate_add,
          List.append_assoc] using h

theorem framedCellCost_le (xs : List (Bool × Bool)) :
    framedCellCost xs ≤ 10 * xs.length + 3 := by
  induction xs with
  | nil => simp [framedCellCost]
  | cons x xs ih =>
      rcases x with ⟨a,b⟩
      cases a <;> cases b <;> simp [framedCellCost] <;> omega

theorem framedCellStream_ternary (xs : List SparseCode.F3) :
    framedCellStream (xs.map ternaryCell) =
      xs.flatMap (fun x => Encoding.frame (SubexpEnumerationPayload.scalarBits x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, framedCellStream, List.flatMap_cons, ih,
        ← ternaryCell_encoding]
      rfl

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
