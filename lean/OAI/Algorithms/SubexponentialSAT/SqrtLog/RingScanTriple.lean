import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanSum

namespace OAI.Algorithms

/-! A native three-scalar product and accumulator step. Triples are serialized
as consecutive fixed-width words; both width and triple count remain data. -/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev scalarMul : Cmd 8 15 := .call (ProgramLinking.liftProgram
  ModularRingPrograms.wordMulProgram id scalarStacks)

theorem scalarMul_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (regs : Fin 8 → Bool) (x y : Word (baseWidth p t))
    (xs ys out count width : List Bool) :
    ∃ n ≤ 6000 * (baseWidth p t + 1)^2, ∃ finalRegs,
      Eval scalarMul n
        (addState regs M.bits x.val y.val xs ys out count width)
        (addState finalRegs M.bits (SubexpPreparedQuartic.wordMul p t M x y).1.val []
          xs ys out count width) := by
  obtain ⟨rf, n, hn, ht⟩ := SubexpScalarMachine.wordMul_run p t M regs x y
  have he := eval_call_lifted ModularRingPrograms.wordMulProgram id scalarStacks
    (addState regs M.bits x.val y.val xs ys out count width)
    Function.injective_id scalarStacks_injective
    (a := ⟨regs, ModularRingPrograms.extendSeven
      (ModularRingPrograms.scalarInput x.val y.val M.bits) []⟩)
    (b := ⟨rf, ModularRingPrograms.extendSeven
      (ModularRingPrograms.scalarInput (SubexpPreparedQuartic.wordMul p t M x y).1.val [] M.bits) []⟩) ht
  refine ⟨n, hn, rf, ?_⟩
  simpa only [embed_scalar] using he

def loadHeadStacks : Fin 5 → Fin 15 := ![9, 0, 12, 13, 14]
theorem loadHeadStacks_injective : Function.Injective loadHeadStacks := by decide
abbrev loadHead : Cmd 8 15 := .call (ProgramLinking.liftProgram
  loadWordProgram loadRegisters loadHeadStacks)

private theorem embed_loadHead (regs : Fin 8 → Bool) (v pr : Bool)
    (modulus oldLeft newLeft right xs oldYs newYs out count width : List Bool) :
    embedState loadRegisters loadHeadStacks
      (addState regs modulus oldLeft right xs oldYs out count width)
      (loadState ![v, pr] newYs newLeft width [] []) =
      addState (Function.update (Function.update regs 1 v) 3 pr)
        modulus newLeft right xs newYs out count width := by
  apply embedState_eq_of_ports _ _ _ _ _ loadRegisters_injective loadHeadStacks_injective
  · intro i; fin_cases i <;> simp [loadRegisters, loadState, addState]
  · intro i hi
    have h1 : i ≠ 1 := fun h => hi ⟨0, h.symm⟩
    have h3 : i ≠ 3 := fun h => hi ⟨1, h.symm⟩
    simp [addState, h1, h3]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨1, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨0, h.symm⟩
    simp [addState, addTapes, h0, h9]

theorem loadHead_eval (regs : Fin 8 → Bool)
    (modulus word tail right xs out count width : List Bool)
    (hwidth : width.length = word.length) :
    Eval loadHead (14 * word.length + 12)
      (addState regs modulus [] right xs (word ++ tail) out count width)
      (addState (readRegs regs 1 3 none) modulus word right xs tail out count width) := by
  have ht := loadWordProgram_trace ![regs 1, regs 3] word tail [] width hwidth
  have he := eval_call_lifted loadWordProgram loadRegisters loadHeadStacks
    (addState regs modulus [] right xs (word ++ tail) out count width)
    loadRegisters_injective loadHeadStacks_injective ht
  have hr : readRegs (![regs 1, regs 3] : Fin 2 → Bool) 0 1 none = ![false,false] := by
    funext i; fin_cases i <;> rfl
  have hu : Function.update (Function.update regs 1 (regs 1)) 3 (regs 3) = regs := by simp
  have hf : Function.update (Function.update regs 1 false) 3 false = readRegs regs 1 3 none := rfl
  simpa only [hr, embed_loadHead, List.append_nil, hu, hf] using he

abbrev restoreAccumulator : Cmd 8 15 := .call (transferProgram 10 1 1 3)

private theorem restore_stacks (modulus term xs ys saved count width : List Bool) :
    transferStacks (10 : Fin 15) 1 (addTapes modulus term [] xs ys saved count width) =
      addTapes modulus term saved.reverse xs ys [] count width := by
  funext i
  by_cases h1 : i = 1
  · subst i; simp [transferStacks, addTapes]
  · by_cases h10 : i = 10
    · subst i; simp [transferStacks, addTapes]
    · simp [transferStacks, addTapes, h1, h10]

theorem restoreAccumulator_eval (regs : Fin 8 → Bool)
    (modulus term xs ys saved count width : List Bool) :
    Eval restoreAccumulator (3 * saved.length + 3)
      (addState regs modulus term [] xs ys saved count width)
      (addState (readRegs regs 1 3 none) modulus term saved.reverse xs ys [] count width) := by
  have ht := transferProgram_trace (10 : Fin 15) 1 (1 : Fin 8) 3
    (by decide) (by decide) regs (addTapes modulus term [] xs ys saved count width)
  have hh := halt_after_trace _ ht 3 rfl rfl
  apply Eval.call
  simpa only [addState, StructuredProgram.State.withPC, transferResult, restore_stacks,
    show addTapes modulus term [] xs ys saved count width 10 = saved from rfl,
    Nat.add_assoc] using hh

abbrev tripleStep : Cmd 8 15 :=
  .seq emitReverse (.seq loadHead (.seq loadY (.seq scalarMul
    (.seq loadY (.seq scalarMul (.seq restoreAccumulator scalarAdd))))))

def tripleProduct (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (a b c : Word (baseWidth p t)) : Word (baseWidth p t) :=
  (SubexpPreparedQuartic.wordMul p t M (SubexpPreparedQuartic.wordMul p t M a b).1 c).1

theorem tripleStep_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (regs : Fin 8 → Bool) (a b c seed : Word (baseWidth p t))
    (tail count width : List Bool) (hwidth : width.length = baseWidth p t) :
    ∃ n ≤ 18000 * (baseWidth p t + 1)^2 + 48 * baseWidth p t + 42,
      ∃ finalRegs, Eval tripleStep n
        (addState regs M.bits seed.val [] [] (a.val ++ (b.val ++ (c.val ++ tail))) [] count width)
        (addState finalRegs M.bits
          (SubexpPreparedQuartic.wordAdd p t M (tripleProduct p t M a b c) seed).1.val
          [] [] tail [] count width) := by
  let ab := (SubexpPreparedQuartic.wordMul p t M a b).1
  let abc := tripleProduct p t M a b c
  have hs := emitReverse_eval regs M.bits seed.val []
    (a.val ++ (b.val ++ (c.val ++ tail))) [] count width
  simp only [List.append_nil] at hs
  have hl := loadHead_eval (readRegs regs 1 3 none) M.bits a.val
    (b.val ++ (c.val ++ tail)) [] [] seed.val.reverse count width (hwidth.trans a.property.symm)
  have hr := loadY_eval (readRegs regs 1 3 none) M.bits a.val b.val
    (c.val ++ tail) [] seed.val.reverse count width (hwidth.trans b.property.symm)
  obtain ⟨n₁, hn₁, r₁, hm₁⟩ := scalarMul_eval p t M (readRegs regs 1 3 none)
    a b [] (c.val ++ tail) seed.val.reverse count width
  have hc := loadY_eval r₁ M.bits ab.val c.val tail [] seed.val.reverse count width
    (hwidth.trans c.property.symm)
  obtain ⟨n₂, hn₂, r₂, hm₂⟩ := scalarMul_eval p t M (readRegs r₁ 1 3 none)
    ab c [] tail seed.val.reverse count width
  have hrestore := restoreAccumulator_eval r₂ M.bits abc.val [] tail seed.val.reverse count width
  simp only [List.length_reverse, List.reverse_reverse] at hrestore
  obtain ⟨n₃, hn₃, r₃, ha⟩ := scalarAdd_eval p t M (readRegs r₂ 1 3 none)
    abc seed [] tail [] count width
  simp only [readRegs_reset] at hl hr
  have total := hs.seq (hl.seq (hr.seq (hm₁.seq (hc.seq (hm₂.seq (hrestore.seq ha))))))
  refine ⟨_, ?_, r₃, total⟩
  simp only [a.property, b.property, c.property, seed.property]
  omega

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
