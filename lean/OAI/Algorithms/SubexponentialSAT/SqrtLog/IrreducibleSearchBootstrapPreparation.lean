import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrapPrimitives
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchEnumerationCost

namespace OAI.Algorithms


/-! A fixed framed call generates an ordered table from a runtime unary depth.
Only its output and depth ports change; the generator's sentinel is paid for
and cleared before returning. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open BitProgram StructuredCalls
open Subexp.TupleProgram SubexpOrderedTupleData
open SubexpEnumerationPayload SubexpTupleRefinement

def alphabetWord : List Bool :=
  ProgramEncoding.encodeRecords IrreducibleSearchEnumeration.alphabet

def tableWord (d : ℕ) : List Bool := ProgramEncoding.encodeRecords
  ((IrreducibleSearch.candidates d).map (encodeTuple (scalarCode 3)))

def generatorOut (candidate : Bool) : Fin 28 := if candidate then 24 else 20

def generatorRegs (i : Fin 10) : Fin 22 := Fin.castAdd 12 i

theorem generatorRegs_injective : Function.Injective generatorRegs :=
  Fin.castAdd_injective _ _

def generatorMap (candidate : Bool) : Fin 9 → Fin 28 :=
  ![generatorOut candidate, 10, 0, 1, 2, 3, 4, 5, 6]

theorem generatorMap_injective (candidate : Bool) :
    Function.Injective (generatorMap candidate) := by
  cases candidate <;> decide

def GeneratorReady (candidate : Bool) (a : Data) : Prop :=
  a.stacks 10 = alphabetWord ∧
  (∀ i : Fin 28, i.val < 6 → a.stacks i = []) ∧
  a.stacks (generatorOut candidate) = []

abbrev generateAt (candidate : Bool) : Cmd 22 28 :=
  .seq (.call (ProgramLinking.liftProgram IrreducibleSearchEnumeration.program
    generatorRegs (generatorMap candidate))) (clearCmd 3)

theorem generateAt_eval (candidate : Bool) (a : Data) (ha : GeneratorReady candidate a) :
    ∃ t rf, Eval (generateAt candidate) t a
      ⟨rf, Function.update
        (Function.update a.stacks (generatorOut candidate) (tableWord (a.stacks 6).length))
        6 []⟩ ∧
      t ≤ IrreducibleSearchEnumeration.cost (a.stacks 6).length + 5 := by
  classical
  let small : State 10 9 :=
    ⟨fun i => a.regs (generatorRegs i), fun i => a.stacks (generatorMap candidate i)⟩
  have ha10 := ha.1
  have ha0 := ha.2.1 0 (by decide)
  have ha1 := ha.2.1 1 (by decide)
  have ha2 := ha.2.1 2 (by decide)
  have ha3 := ha.2.1 3 (by decide)
  have ha4 := ha.2.1 4 (by decide)
  have ha5 := ha.2.1 5 (by decide)
  have hl : outerInvariant IrreducibleSearchEnumeration.alphabet
      (a.stacks 6) (small.regs 9) small := by
    simp [outerInvariant, small, generatorMap, ha.1, alphabetWord, ha1, ha2, ha4, ha5]
  obtain ⟨next, hn, t, ht, he⟩ := IrreducibleSearchEnumeration.program_runsIn
    IrreducibleSearchEnumeration.alphabet (a.stacks 6) (small.regs 9) small hl
    (by simpa [small, generatorMap] using ha.2.2)
    (by simpa [small, generatorMap] using ha0)
    (by simpa [small, generatorMap] using ha3)
  have hstart : embedState generatorRegs (generatorMap candidate) a small = a := by
    apply embedState_eq_of_ports generatorRegs (generatorMap candidate) a a small
      generatorRegs_injective (generatorMap_injective candidate)
    all_goals intros; rfl
  rcases hn with ⟨⟨h1,h3,h4,h6,h7,h8,h9⟩,h0,h2,h5⟩
  have hout : next.stacks 0 = tableWord (a.stacks 6).length := by
    simpa only [tableWord, IrreducibleSearchEnumeration.alphabet,
      orderedRows_encoded, IrreducibleSearch.candidates] using h0
  let mid : Data := ⟨Function.extend generatorRegs next.regs a.regs,
    Function.update (Function.update
      (Function.update a.stacks (generatorOut candidate) (tableWord (a.stacks 6).length))
      6 []) 3 [false]⟩
  have hend : embedState generatorRegs (generatorMap candidate) a next = mid := by
    apply embedState_eq_of_ports generatorRegs (generatorMap candidate) a mid next
      generatorRegs_injective (generatorMap_injective candidate)
    · intro i
      exact generatorRegs_injective.extend_apply _ _ _
    · intro i hi
      exact Function.extend_apply' _ _ _ hi
    · intro i
      fin_cases i <;> cases candidate <;>
        simp_all [mid, generatorMap, generatorOut, alphabetWord]
    · intro i hi
      have ho : i ≠ generatorOut candidate := fun h => hi ⟨0, h.symm⟩
      have h6' : i ≠ 6 := fun h => hi ⟨8, h.symm⟩
      have h3' : i ≠ 3 := fun h => hi ⟨5, h.symm⟩
      simp [mid, ho, h6', h3']
  have hcall := eval_call_lifted IrreducibleSearchEnumeration.program
    generatorRegs (generatorMap candidate) a generatorRegs_injective
    (generatorMap_injective candidate) he
  rw [hstart, hend] at hcall
  have hc := clearCmd_eval 3 mid
  have hfinal : Function.update mid.stacks 3 [] =
      Function.update
        (Function.update a.stacks (generatorOut candidate) (tableWord (a.stacks 6).length))
        6 [] := by
    funext i
    by_cases hi : i = 3
    · subst i
      cases candidate <;> simp [mid, generatorOut, ha3]
    · simp [mid, hi]
  refine ⟨t + 5, readRegs mid.regs 0 1 none, ?_, ?_⟩
  · simpa only [generateAt, show (mid.stacks 3).length = 1 by simp [mid],
      show 2 * 1 + 3 = 5 from rfl, hfinal] using hcall.seq hc
  · simpa only [IrreducibleSearchEnumeration.cost] using Nat.add_le_add_right ht 5

end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap


/-! Paid construction of both search tables from a single unary depth word. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open BitProgram StructuredCalls


def layout (depth count candidates factors alphabet fuel : List Bool) : Fin 28 → List Bool :=
  fun i => if i = 14 then depth else if i = 22 then count else if i = 24 then candidates
    else if i = 20 then factors else if i = 10 then alphabet else if i = 6 then fuel else []

abbrev state (depth count candidates factors alphabet fuel : List Bool)
    (regs : Fin 22 → Bool) : Data := ⟨regs, layout depth count candidates factors alphabet fuel⟩

@[simp] theorem layout14 (d c a b w f : List Bool) : layout d c a b w f 14 = d := rfl
@[simp] theorem layout22 (d c a b w f : List Bool) : layout d c a b w f 22 = c := rfl
@[simp] theorem layout24 (d c a b w f : List Bool) : layout d c a b w f 24 = a := rfl
@[simp] theorem layout20 (d c a b w f : List Bool) : layout d c a b w f 20 = b := rfl
@[simp] theorem layout10 (d c a b w f : List Bool) : layout d c a b w f 10 = w := rfl
@[simp] theorem layout6 (d c a b w f : List Bool) : layout d c a b w f 6 = f := rfl
@[simp] theorem layout7 (d c a b w f : List Bool) : layout d c a b w f 7 = [] := rfl

@[simp] theorem layout_update22 (d c a b w f x : List Bool) :
    Function.update (layout d c a b w f) 22 x = layout d x a b w f := by
  funext i; fin_cases i <;> simp [layout]

@[simp] theorem layout_update24 (d c a b w f x : List Bool) :
    Function.update (layout d c a b w f) 24 x = layout d c x b w f := by
  funext i; fin_cases i <;> simp [layout]

@[simp] theorem layout_update20 (d c a b w f x : List Bool) :
    Function.update (layout d c a b w f) 20 x = layout d c a x w f := by
  funext i; fin_cases i <;> simp [layout]

@[simp] theorem layout_update10 (d c a b w f x : List Bool) :
    Function.update (layout d c a b w f) 10 x = layout d c a b x f := by
  funext i; fin_cases i <;> simp [layout]

@[simp] theorem layout_update6 (d c a b w f x : List Bool) :
    Function.update (layout d c a b w f) 6 x = layout d c a b w x := by
  funext i; fin_cases i <;> simp [layout]

theorem layout_low (d c a b w f : List Bool) (i : Fin 28) (hi : i.val < 6) :
    layout d c a b w f i = [] := by
  fin_cases i <;> simp_all [layout]

abbrev command : Cmd 22 28 :=
  .seq (copyCmd 14 22)
  (.seq (Subexp.TupleProgram.pushConst 22 0 false)
  (.seq (pushWord 10 alphabetWord)
  (.seq (copyCmd 14 6)
  (.seq (generateAt true)
  (.seq (copyCmd 22 6)
  (.seq (copyCmd 22 6)
  (.seq (generateAt false)
  (.seq (clearCmd 10) RegisterResetProgram.all))))))))

def cost (d : ℕ) : ℕ := IrreducibleSearchEnumeration.cost d +
  IrreducibleSearchEnumeration.cost ((d + 1) + (d + 1)) +
  28 * d + 4 * alphabetWord.length + 71

/-- Only the input depth is supplied. The tables, count, scratch cleanup, and
register reset are all produced by the displayed fixed command. -/
theorem command_eval (depth : List Bool) (regs : Fin 22 → Bool) :
    ∃ t, t ≤ cost depth.length ∧
      Eval command t (state depth [] [] [] [] [] regs)
        (state depth (false :: depth) (tableWord depth.length)
          (tableWord ((depth.length + 1) + (depth.length + 1))) [] [] (fun _ => false)) := by
  let a0 := state depth [] [] [] [] [] regs
  let r1 := readRegs regs 0 1 none
  let a1 := state depth depth [] [] [] [] r1
  have e1 : Eval (copyCmd 14 22) (7 * depth.length + 5) a0 a1 := by
    simpa only [a0, a1, r1, state, layout14, layout22, List.append_nil, layout_update22]
      using copyCmd_eval 14 22 a0 (by decide) (by decide) (by decide) rfl
  let r2 := Function.update r1 0 false
  let a2 := state depth (false :: depth) [] [] [] [] r2
  have e2 : Eval (Subexp.TupleProgram.pushConst 22 0 false) 2 a1 a2 := by
    simpa only [a1, a2, r2, state, Subexp.TupleProgram.pushedState, layout22, layout_update22]
      using Subexp.TupleProgram.pushConst_eval 22 (0 : Fin 22) false a1
  obtain ⟨r3, e3'⟩ := pushWord_eval 10 alphabetWord a2
  let a3 := state depth (false :: depth) [] [] alphabetWord [] r3
  have e3 : Eval (pushWord 10 alphabetWord) (2 * alphabetWord.length) a2 a3 := by
    simpa only [a2, a3, state, layout10, List.append_nil, layout_update10] using e3'
  let r4 := readRegs r3 0 1 none
  let a4 := state depth (false :: depth) [] [] alphabetWord depth r4
  have e4 : Eval (copyCmd 14 6) (7 * depth.length + 5) a3 a4 := by
    simpa only [a3, a4, r4, state, layout14, layout6, List.append_nil, layout_update6]
      using copyCmd_eval 14 6 a3 (by decide) (by decide) (by decide) rfl
  have ready4 : GeneratorReady true a4 := by
    refine ⟨rfl, ?_, rfl⟩
    exact layout_low _ _ _ _ _ _
  obtain ⟨t5, r5, e5', ht5⟩ := generateAt_eval true a4 ready4
  let a5 := state depth (false :: depth) (tableWord depth.length) [] alphabetWord [] r5
  have e5 : Eval (generateAt true) t5 a4 a5 := by
    simpa [a4, a5, state, generatorOut] using e5'
  have ht5' : t5 ≤ IrreducibleSearchEnumeration.cost depth.length + 5 := ht5
  let r6 := readRegs r5 0 1 none
  let a6 := state depth (false :: depth) (tableWord depth.length) [] alphabetWord
    (false :: depth) r6
  have e6 : Eval (copyCmd 22 6) (7 * (depth.length + 1) + 5) a5 a6 := by
    simpa only [a5, a6, r6, state, layout22, layout6, List.append_nil,
      List.length_cons, layout_update6]
      using copyCmd_eval 22 6 a5 (by decide) (by decide) (by decide) rfl
  let r7 := readRegs r6 0 1 none
  let a7 := state depth (false :: depth) (tableWord depth.length) [] alphabetWord
    ((false :: depth) ++ (false :: depth)) r7
  have e7 : Eval (copyCmd 22 6) (7 * (depth.length + 1) + 5) a6 a7 := by
    simpa only [a6, a7, r7, state, layout22, layout6, List.length_cons, layout_update6]
      using copyCmd_eval 22 6 a6 (by decide) (by decide) (by decide) rfl
  have ready7 : GeneratorReady false a7 := by
    refine ⟨rfl, ?_, rfl⟩
    exact layout_low _ _ _ _ _ _
  obtain ⟨t8, r8, e8', ht8⟩ := generateAt_eval false a7 ready7
  let a8 := state depth (false :: depth) (tableWord depth.length)
    (tableWord ((depth.length + 1) + (depth.length + 1))) alphabetWord [] r8
  have e8 : Eval (generateAt false) t8 a7 a8 := by
    simpa [a7, a8, state, generatorOut, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using e8'
  have ht8' : t8 ≤ IrreducibleSearchEnumeration.cost
      ((depth.length + 1) + (depth.length + 1)) + 5 := by
    simpa only [a7, state, layout6, List.length_append, List.length_cons] using ht8
  let r9 := readRegs r8 0 1 none
  let a9 := state depth (false :: depth) (tableWord depth.length)
    (tableWord ((depth.length + 1) + (depth.length + 1))) [] [] r9
  have e9 : Eval (clearCmd 10) (2 * alphabetWord.length + 3) a8 a9 := by
    simpa only [a8, a9, r9, state, layout10, layout_update10] using clearCmd_eval 10 a8
  have e10 := RegisterResetProgram.all_eval a9
  refine ⟨_, ?_, e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq
    (e7.seq (e8.seq (e9.seq e10))))))))⟩
  dsimp only [cost]
  omega

end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

end OAI.Algorithms
