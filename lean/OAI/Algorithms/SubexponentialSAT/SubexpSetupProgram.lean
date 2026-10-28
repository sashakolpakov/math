import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
import OAI.Algorithms.SubexponentialSAT.SubexpSetupFrames
import OAI.Algorithms.SubexponentialSAT.SubexpGuardProgram
import OAI.Algorithms.SubexponentialSAT.SubexpMainProgram
import OAI.Algorithms.SubexponentialSAT.SparsificationThresholdProgram
import OAI.Algorithms.SubexponentialSAT.SparsificationThresholdTable
import OAI.Algorithms.SubexponentialSAT.SubexpPrimeIntervalProgram
import OAI.Algorithms.SubexponentialSAT.SubexpIncidenceGuardProgram
import OAI.Algorithms.SubexponentialSAT.SubexpGuardTailProgram
import OAI.Algorithms.SubexponentialSAT.SubexpFieldParameterProgram
import OAI.Algorithms.SubexponentialSAT.SubexpCeilingProgram
import OAI.Algorithms.SubexponentialSAT.SubexpBlockParameterProgram
import OAI.Algorithms.SubexponentialSAT.DyadicReadiness

namespace OAI.Algorithms

/-!
# A closed program for the growing numerical setup

The clause width, dyadic control parameter, and extra workspace are fixed before
the input. Every phase below is a named finite bit program. Inputs are copied
from persistent storage into a reusable workspace, outputs are copied back,
and the entire local subroutine workspace is physically cleared after return.

The protected threshold extension is disjoint from both ordinary workspace and
the thirty-two persistent scalar slots. Its producer is the fixed-width
threshold-table compiler.
-/

namespace SubexponentialSAT.SubexpSetupProgram

open BitProgram StructuredCalls SubexpSetupStorage

/-- All fields are fixed before reading the input formula. -/
structure Config where
  k : ℕ
  T : ℕ
  extra : ℕ
  width_ge_two : 2 ≤ k
  control : SparsificationBudgetProgram.Control k T

def occurrenceSlots (c : Config) : ℕ :=
  ArithmeticExpressionProgram.slots (SparsificationThresholdProgram.occurrenceExpr c.k)

def thresholdCount (c : Config) : ℕ := c.k - 1
def tableSlots (c : Config) : ℕ :=
  SparsificationThresholdTable.workSlots (SparsificationThresholdTable.expressions c.k) +
    thresholdCount c
def helperSize (c : Config) : ℕ := 128 + occurrenceSlots c + tableSlots c + c.extra
def stackCount (c : Config) : ℕ := helperSize c + thresholdCount c + 32

abbrev SetupState (c : Config) := State 16 (stackCount c)
abbrev SetupCmd (c : Config) := Cmd 16 (stackCount c)

def persistent (c : Config) (i : Fin 32) : Fin (stackCount c) :=
  ⟨helperSize c + thresholdCount c + i.val, by unfold stackCount; omega⟩

def threshold (c : Config) (i : Fin (thresholdCount c)) : Fin (stackCount c) :=
  ⟨helperSize c + i.val, by unfold stackCount; omega⟩

def workPort (c : Config) {s : ℕ} (hs : s < helperSize c) (i : Fin s) :
    Fin (stackCount c) := ⟨i.val, by unfold stackCount; omega⟩

def temporary (c : Config) : Fin (stackCount c) :=
  ⟨helperSize c - 1, by unfold stackCount helperSize; omega⟩

theorem workPort_injective (c : Config) {s : ℕ} (hs : s < helperSize c) :
    Function.Injective (workPort c hs) := by
  intro i j h
  have hv := congrArg (fun x : Fin (stackCount c) => x.val) h
  exact Fin.ext hv

def registerPort {r : ℕ} (hr : r ≤ 9) (i : Fin r) : Fin 16 :=
  i.castLE (by omega)

theorem registerPort_injective {r : ℕ} (hr : r ≤ 9) :
    Function.Injective (registerPort hr) := by
  intro i j h
  have hv := congrArg (fun x : Fin 16 => x.val) h
  exact Fin.ext hv

/-- The decision bit is separated from the arithmetic work registers. -/
def guardRegister (i : Fin 9) : Fin 16 := if i = 8 then 15 else i.castLE (by decide)

theorem guardRegister_injective : Function.Injective guardRegister := by decide

def localPorts (c : Config) {s : ℕ} (hs : s < helperSize c) :
    List (Fin (stackCount c)) := List.ofFn (workPort c hs)

def inputCopies (c : Config) {s : ℕ} (hs : s < helperSize c)
    (inputs : List (Fin (stackCount c) × Fin s)) :
    List (Fin (stackCount c) × Fin (stackCount c)) :=
  inputs.map (fun p => (p.1, workPort c hs p.2))

def outputCopies (c : Config) {s : ℕ} (hs : s < helperSize c)
    (outputs : List (Fin s × Fin (stackCount c))) :
    List (Fin (stackCount c) × Fin (stackCount c)) :=
  outputs.map (fun p => (workPort c hs p.1, p.2))

/-- A statically allocated real subroutine call, with physical copy and cleanup
instructions. The program argument is instantiated below by named bit tables. -/
abbrev stage (c : Config) {r s l : ℕ} (p : Program r s l)
    (register : Fin r → Fin 16) (hs : s < helperSize c)
    (inputs : List (Fin (stackCount c) × Fin s))
    (outputs : List (Fin s × Fin (stackCount c))) : SetupCmd c :=
  isolated p register (workPort c hs) (temporary c) (localPorts c hs)
    (inputCopies c hs inputs) (outputCopies c hs outputs)

theorem small_fits (c : Config) {s : ℕ} (hs : s ≤ 32) : s < helperSize c := by
  unfold helperSize
  omega

def early (c : Config) : SetupCmd c :=
  stage c (compiled SubexpGuardProgram.earlyGuard 0 1) guardRegister
    (small_fits c (by decide)) [(persistent c 4, 0)] []

def selectM (c : Config) : SetupCmd c :=
  stage c (SparsificationBudgetProgram.program c.T) (registerPort (by decide))
    (small_fits c (by decide)) [(persistent c 4, 0)] [(2, persistent c 23)]

def occurrence (c : Config) : SetupCmd c :=
  let e := SparsificationThresholdProgram.occurrenceExpr c.k
  let h : 2 ≤ ArithmeticExpressionProgram.slots e :=
    le_trans (by decide) (ArithmeticExpressionProgram.slots_ge e)
  stage c (SparsificationThresholdProgram.occurrenceProgram c.k) (registerPort (by decide))
    (by unfold helperSize occurrenceSlots; omega)
    [(persistent c 23, ArithmeticExpressionProgram.inputPort h)]
    [(ArithmeticExpressionProgram.outputPort h, persistent c 24)]

def thresholdTable (c : Config) : SetupCmd c :=
  stage c (SparsificationThresholdTable.thresholdProgram c.k) (registerPort (by decide))
    (by change tableSlots c < helperSize c; unfold helperSize; omega)
    [(persistent c 23,
      SparsificationThresholdTable.inputPort (SparsificationThresholdTable.expressions c.k))]
    (List.ofFn (fun i : Fin (thresholdCount c) =>
      (SparsificationThresholdTable.bankPort (SparsificationThresholdTable.expressions c.k) i,
        threshold c i)))

def incidence (c : Config) : SetupCmd c :=
  stage c SubexpIncidenceGuardProgram.program (registerPort (by decide))
    (small_fits c (by decide)) [(persistent c 5, 0), (persistent c 24, 1)]
    [(2, persistent c 16)]

def prime (c : Config) : SetupCmd c :=
  stage c SubexpPrimeIntervalProgram.primeSelectProgram (registerPort (by decide))
    (small_fits c (by decide)) [(persistent c 5, 0)] [(9, persistent c 6)]

def field (c : Config) : SetupCmd c :=
  stage c (SubexpFieldParameterProgram.program c.k) (registerPort (by decide))
    (small_fits c (by decide)) [(persistent c 6, 0), (persistent c 16, 1)]
    [(4, persistent c 17), (7, persistent c 25)]

def dimension (c : Config) : SetupCmd c :=
  stage c SubexpCeilingProgram.program (registerPort (by decide))
    (small_fits c (by decide)) [(persistent c 5, 5), (persistent c 2, 6)]
    [(7, persistent c 19)]

def block (c : Config) : SetupCmd c :=
  stage c (SubexpBlockParameterProgram.program c.k) (registerPort (by decide))
    (small_fits c (by decide))
    [(persistent c 4, 0), (persistent c 16, 1), (persistent c 17, 2)]
    [(7, persistent c 18), (14, persistent c 20)]

def tailOperands (c : Config) : SetupCmd c :=
  stage c SubexpGuardTailProgram.program (registerPort (by decide))
    (small_fits c (by decide))
    [(persistent c 25, 0), (persistent c 17, 1), (persistent c 16, 2), (persistent c 4, 3)]
    [(4, persistent c 26), (5, persistent c 27)]

def precision (c : Config) : SetupCmd c :=
  stage c (CounterPrograms.rippleProgram true) (registerPort (by decide))
    (small_fits c (by decide)) [(persistent c 19, 0)] [(0, persistent c 22)]

def inverseExponent (c : Config) : SetupCmd c :=
  stage c (CounterPrograms.rippleProgram false) (registerPort (by decide))
    (small_fits c (by decide)) [(persistent c 17, 0)] [(0, persistent c 29)]

def colors (c : Config) : SetupCmd c :=
  .seq (clearMany [temporary c, persistent c 21])
    (copyMany (temporary c) [(persistent c 4, persistent c 21)])

def cutoff (c : Config) : SetupCmd c :=
  .seq (clearMany [persistent c 28])
    (.base (SubexpGuardProgram.loadThirtyTwo 0 (persistent c 28)))

def readyGuard (c : Config) : SetupCmd c :=
  stage c (compiled SubexpGuardProgram.guard 0 1) guardRegister
    (small_fits c (by decide))
    [(persistent c 4, 0), (persistent c 28, 1), (persistent c 26, 2),
      (persistent c 27, 3), (persistent c 19, 4), (persistent c 20, 5)] []

/-- Every listed arithmetic operation is a concrete previously defined program. -/
def numericSetup (c : Config) : SetupCmd c :=
  .seq (selectM c) (.seq (occurrence c) (.seq (incidence c)
    (.seq (prime c) (.seq (field c) (.seq (dimension c) (.seq (block c)
      (.seq (tailOperands c) (.seq (precision c) (.seq (inverseExponent c) (.seq (colors c)
        (cutoff c)))))))))))

def scalarSetup (c : Config) : SetupCmd c :=
  .seq (numericSetup c) (.seq (thresholdTable c) (readyGuard c))

/-- Small-log inputs exit with a false decision bit before positive-divisor
arithmetic is invoked. The good branch computes all scalar guard operands. -/
def scalarCommand (c : Config) : SetupCmd c :=
  .seq (early c) (.ite 15 (scalarSetup c) (.base .skip))

def scalarProgram (c : Config) := compiled (scalarCommand c) (persistent c 0) (persistent c 0)

/-- All ordinary workspace is cleared before the next top-level phase. The
protected threshold extension and persistent slots are outside this list. -/
def workspacePorts (c : Config) : List (Fin (stackCount c)) :=
  List.ofFn (fun i : Fin (helperSize c) =>
    (⟨i.val, by unfold stackCount; omega⟩ : Fin (stackCount c)))

def command (c : Config) : SetupCmd c :=
  .seq (scalarCommand c) (clearMany (workspacePorts c))

def program (c : Config) := compiled (command c) (persistent c 0) (persistent c 0)

/-- The numerical data relation that the closed setup will establish. -/
structure ScalarValues (c : Config) (n : ℕ) (a : SetupState c) : Prop where
  prime : BinaryArithmetic.toNat (a.stacks (persistent c 6)) = SubexpPackingParameters.p n
  M : BinaryArithmetic.toNat (a.stacks (persistent c 23)) = DyadicSchedule.M c.T n
  B : BinaryArithmetic.toNat (a.stacks (persistent c 24)) = DyadicSchedule.B c.k c.T n
  delta : BinaryArithmetic.toNat (a.stacks (persistent c 16)) = DyadicSchedule.delta c.k c.T n
  Q : BinaryArithmetic.toNat (a.stacks (persistent c 17)) = DyadicSchedule.Q n
  R : BinaryArithmetic.toNat (a.stacks (persistent c 25)) = DyadicSchedule.R c.k c.T n
  N : BinaryArithmetic.toNat (a.stacks (persistent c 18)) = DyadicSchedule.N c.k c.T n
  D : BinaryArithmetic.toNat (a.stacks (persistent c 19)) = SubexpPackingParameters.D n
  Dstar : BinaryArithmetic.toNat (a.stacks (persistent c 20)) = DyadicSchedule.Dstar c.k c.T n
  square : BinaryArithmetic.toNat (a.stacks (persistent c 26)) = DyadicSchedule.R c.k c.T n ^ 2
  tail : BinaryArithmetic.toNat (a.stacks (persistent c 27)) =
    16 * DyadicSchedule.Q n * DyadicSchedule.delta c.k c.T n * SubexpPackingParameters.s n
  colors : BinaryArithmetic.toNat (a.stacks (persistent c 21)) = SubexpPackingParameters.r n
  precision : BinaryArithmetic.toNat (a.stacks (persistent c 22)) = SubexpPackingParameters.D n + 1
  inverseExponent : BinaryArithmetic.toNat (a.stacks (persistent c 29)) =
    SubexpPackingParameters.p n ^ 4 - 2

end SubexponentialSAT.SubexpSetupProgram

end OAI.Algorithms
