import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanLoad
import OAI.Algorithms.SubexponentialSAT.SubexpScalarMachine
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Native scalar addition inside a flat, runtime-sized coefficient scan. -/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- The lower eight stacks are precisely the audited scalar ABI. The remaining
seven contain the flat input vectors, output accumulator, and unary controls. -/
def addTapes (modulus left right xs ys out count width : List Bool) : Fin 15 → List Bool :=
  fun i => if i = 0 then left else if i = 1 then right else if i = 5 then modulus
    else if i = 8 then xs else if i = 9 then ys else if i = 10 then out
    else if i = 11 then count else if i = 12 then width else []

def addState (regs : Fin 8 → Bool) (modulus left right xs ys out count width : List Bool) :
    State 8 15 := ⟨regs, addTapes modulus left right xs ys out count width⟩

def loadRegisters : Fin 2 → Fin 8 := ![1, 3]
def loadXStacks : Fin 5 → Fin 15 := ![8, 0, 12, 13, 14]
def loadYStacks : Fin 5 → Fin 15 := ![9, 1, 12, 13, 14]

theorem loadRegisters_injective : Function.Injective loadRegisters := by decide
theorem loadXStacks_injective : Function.Injective loadXStacks := by decide
theorem loadYStacks_injective : Function.Injective loadYStacks := by decide

abbrev loadX : Cmd 8 15 := .call (ProgramLinking.liftProgram loadWordProgram loadRegisters loadXStacks)
abbrev loadY : Cmd 8 15 := .call (ProgramLinking.liftProgram loadWordProgram loadRegisters loadYStacks)

private theorem embed_loadX (regs : Fin 8 → Bool) (v pr : Bool)
    (modulus oldLeft newLeft right oldXs newXs ys out count width : List Bool) :
    embedState loadRegisters loadXStacks
      (addState regs modulus oldLeft right oldXs ys out count width)
      (loadState ![v, pr] newXs newLeft width [] []) =
      addState (Function.update (Function.update regs 1 v) 3 pr)
        modulus newLeft right newXs ys out count width := by
  apply embedState_eq_of_ports _ _ _ _ _ loadRegisters_injective loadXStacks_injective
  · intro i; fin_cases i <;> simp [loadRegisters, loadState, addState]
  · intro i hi
    have h1 : i ≠ 1 := fun h => hi ⟨0, h.symm⟩
    have h3 : i ≠ 3 := fun h => hi ⟨1, h.symm⟩
    simp [addState, h1, h3]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨1, h.symm⟩
    have h8 : i ≠ 8 := fun h => hi ⟨0, h.symm⟩
    simp [addState, addTapes, h0, h8]

private theorem embed_loadY (regs : Fin 8 → Bool) (v pr : Bool)
    (modulus left oldRight newRight xs oldYs newYs out count width : List Bool) :
    embedState loadRegisters loadYStacks
      (addState regs modulus left oldRight xs oldYs out count width)
      (loadState ![v, pr] newYs newRight width [] []) =
      addState (Function.update (Function.update regs 1 v) 3 pr)
        modulus left newRight xs newYs out count width := by
  apply embedState_eq_of_ports _ _ _ _ _ loadRegisters_injective loadYStacks_injective
  · intro i; fin_cases i <;> simp [loadRegisters, loadState, addState]
  · intro i hi
    have h1 : i ≠ 1 := fun h => hi ⟨0, h.symm⟩
    have h3 : i ≠ 3 := fun h => hi ⟨1, h.symm⟩
    simp [addState, h1, h3]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨0, h.symm⟩
    simp [addState, addTapes, h1, h9]

private theorem reset_two (v pr : Bool) :
    readRegs (![v, pr] : Fin 2 → Bool) 0 1 none = ![false, false] := by
  funext i; fin_cases i <;> rfl

private theorem update_self_regs (regs : Fin 8 → Bool) :
    Function.update (Function.update regs 1 (regs 1)) 3 (regs 3) = regs := by
  simp

private theorem update_false_regs (regs : Fin 8 → Bool) :
    Function.update (Function.update regs 1 false) 3 false = readRegs regs 1 3 none := rfl

theorem loadX_eval (regs : Fin 8 → Bool)
    (modulus word tail right ys out count width : List Bool)
    (hwidth : width.length = word.length) :
    Eval loadX (14 * word.length + 12)
      (addState regs modulus [] right (word ++ tail) ys out count width)
      (addState (readRegs regs 1 3 none) modulus word right tail ys out count width) := by
  have ht := loadWordProgram_trace ![regs 1, regs 3] word tail [] width hwidth
  have he := eval_call_lifted loadWordProgram loadRegisters loadXStacks
    (addState regs modulus [] right (word ++ tail) ys out count width)
    loadRegisters_injective loadXStacks_injective ht
  simpa only [reset_two, embed_loadX, List.append_nil, update_self_regs, update_false_regs] using he

theorem loadY_eval (regs : Fin 8 → Bool)
    (modulus left word tail xs out count width : List Bool)
    (hwidth : width.length = word.length) :
    Eval loadY (14 * word.length + 12)
      (addState regs modulus left [] xs (word ++ tail) out count width)
      (addState (readRegs regs 1 3 none) modulus left word xs tail out count width) := by
  have ht := loadWordProgram_trace ![regs 1, regs 3] word tail [] width hwidth
  have he := eval_call_lifted loadWordProgram loadRegisters loadYStacks
    (addState regs modulus left [] xs (word ++ tail) out count width)
    loadRegisters_injective loadYStacks_injective ht
  simpa only [reset_two, embed_loadY, List.append_nil, update_self_regs, update_false_regs] using he

def scalarStacks : Fin 8 → Fin 15 := Fin.castAdd 7

theorem scalarStacks_injective : Function.Injective scalarStacks := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 15 => x.val) h)

abbrev scalarAdd : Cmd 8 15 := .call (ProgramLinking.liftProgram
  ModularRingPrograms.wordAddProgram id scalarStacks)

theorem embed_scalar (regs oldRegs : Fin 8 → Bool)
    (modulus left right oldLeft oldRight xs ys out count width : List Bool) :
    embedState id scalarStacks (addState oldRegs modulus oldLeft oldRight xs ys out count width)
      ⟨regs, ModularRingPrograms.extendSeven (ModularRingPrograms.scalarInput left right modulus) []⟩ =
      addState regs modulus left right xs ys out count width := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id scalarStacks_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
    simp [addState, addTapes, h0, h1]

theorem scalarAdd_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (regs : Fin 8 → Bool) (x y : Word (baseWidth p t))
    (xs ys out count width : List Bool) :
    ∃ n ≤ 6000 * (baseWidth p t + 1)^2, ∃ finalRegs,
      Eval scalarAdd n
        (addState regs M.bits x.val y.val xs ys out count width)
        (addState finalRegs M.bits (SubexpPreparedQuartic.wordAdd p t M x y).1.val []
          xs ys out count width) := by
  obtain ⟨rf, n, hn, ht⟩ := SubexpScalarMachine.wordAdd_run p t M regs x y
  have he := eval_call_lifted ModularRingPrograms.wordAddProgram id scalarStacks
    (addState regs M.bits x.val y.val xs ys out count width)
    Function.injective_id scalarStacks_injective
    (a := ⟨regs, ModularRingPrograms.extendSeven
      (ModularRingPrograms.scalarInput x.val y.val M.bits) []⟩)
    (b := ⟨rf, ModularRingPrograms.extendSeven
      (ModularRingPrograms.scalarInput (SubexpPreparedQuartic.wordAdd p t M x y).1.val [] M.bits) []⟩) ht
  refine ⟨n, hn, rf, ?_⟩
  simpa only [embed_scalar] using he

abbrev emitReverse : Cmd 8 15 := .call (transferProgram 0 10 1 3)

private theorem emit_stacks (modulus word xs ys out count width : List Bool) :
    transferStacks (0 : Fin 15) 10 (addTapes modulus word [] xs ys out count width) =
      addTapes modulus [] [] xs ys (word.reverse ++ out) count width := by
  funext i
  by_cases h0 : i = 0
  · subst i; simp [transferStacks, addTapes]
  · by_cases h10 : i = 10
    · subst i; simp [transferStacks, addTapes]
    · simp [transferStacks, addTapes, h0, h10]

theorem emitReverse_eval (regs : Fin 8 → Bool)
    (modulus word xs ys out count width : List Bool) :
    Eval emitReverse (3 * word.length + 3)
      (addState regs modulus word [] xs ys out count width)
      (addState (readRegs regs 1 3 none) modulus [] [] xs ys
        (word.reverse ++ out) count width) := by
  have ht := transferProgram_trace (0 : Fin 15) 10 (1 : Fin 8) 3
    (by decide) (by decide) regs (addTapes modulus word [] xs ys out count width)
  have hh := halt_after_trace _ ht 3 rfl rfl
  apply Eval.call
  simpa only [addState, StructuredProgram.State.withPC, transferResult, emit_stacks,
    show addTapes modulus word [] xs ys out count width 0 = word from rfl,
    Nat.add_assoc] using hh

abbrev addStep : Cmd 8 15 := .seq loadX (.seq loadY (.seq scalarAdd emitReverse))

/-- One real coefficient step, including both dynamic-width loads and output
movement. All input suffixes and unary controls are preserved exactly. -/
theorem addStep_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (regs : Fin 8 → Bool) (x y : Word (baseWidth p t))
    (xs ys out count width : List Bool) (hwidth : width.length = baseWidth p t) :
    ∃ n ≤ 6000 * (baseWidth p t + 1)^2 + 31 * baseWidth p t + 27,
      ∃ finalRegs, Eval addStep n
        (addState regs M.bits [] [] (x.val ++ xs) (y.val ++ ys) out count width)
        (addState finalRegs M.bits [] [] xs ys
          ((SubexpPreparedQuartic.wordAdd p t M x y).1.val.reverse ++ out) count width) := by
  have hx := loadX_eval regs M.bits x.val xs [] (y.val ++ ys) out count width
    (hwidth.trans x.property.symm)
  have hy := loadY_eval (readRegs regs 1 3 none) M.bits x.val y.val ys xs out count width
    (hwidth.trans y.property.symm)
  obtain ⟨n, hn, rf, ha⟩ := scalarAdd_eval p t M (readRegs regs 1 3 none) x y xs ys out count width
  have he := emitReverse_eval rf M.bits (SubexpPreparedQuartic.wordAdd p t M x y).1.val
    xs ys out count width
  have hy' := hy
  simp only [readRegs_reset] at hy'
  have total := hx.seq (hy'.seq (ha.seq he))
  refine ⟨_, ?_, readRegs rf 1 3 none, total⟩
  simp only [x.property, y.property, (SubexpPreparedQuartic.wordAdd p t M x y).1.property]
  omega

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
