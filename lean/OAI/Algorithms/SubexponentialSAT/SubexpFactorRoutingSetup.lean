import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorRoutingCalls

namespace OAI.Algorithms

/-! Actual master copies, numeric conversion, output reversal, and cleanup. -/

namespace SubexponentialSAT.SubexpFactorRoutingSetup

open BitProgram StructuredCalls SubexpScanPrimitives SubexpFactorRoutingControl
open SubexpFactorRoutingCalls

attribute [local simp] Fin.coe_ofNat_eq_mod

def preparedStacks (d : Data) : Fin 48 → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update d.stacks 7 (d.stacks 0)) 8 (d.stacks 1))
      12 (unary (CounterPrograms.value (d.stacks 2)))) 13 (d.stacks 3)) 23 [false]) 6 [false]

def prepareBudget (d : Data) : ℕ :=
  (7 * (d.stacks 0).length + 5) + (7 * (d.stacks 1).length + 5) +
  (7 * (d.stacks 2).length + 5) + CounterConversions.runtimeBound (d.stacks 2) +
  (7 * (d.stacks 3).length + 5) + 4

theorem prepare_eval (d : Data) (hc : Clean d) :
    ∃ n ≤ prepareBudget d, ∃ a : Data, Eval prepare n d a ∧ a.stacks = preparedStacks d := by
  have h6 := hc 6 (by decide)
  have h7 := hc 7 (by decide)
  have h8 := hc 8 (by decide)
  have h12 := hc 12 (by decide)
  have h13 := hc 13 (by decide)
  have h23 := hc 23 (by decide)
  have h24 := hc 24 (by decide)
  have h25 := hc 25 (by decide)
  have h26 := hc 26 (by decide)
  let a := afterCopy d 0 7 0 1
  let b := afterCopy a 1 8 0 1
  let c := afterCopy b 2 24 0 1
  let e := converted c 12
  let f := afterCopy e 3 13 0 1
  let k := Subexp.TupleProgram.pushedState 23 0 false f
  let z := Subexp.TupleProgram.pushedState 6 0 false k
  have he1 := copy_eval d 0 7 (by decide) (by decide) (by decide) h26
  have he2 := copy_eval a 1 8 (by decide) (by decide) (by decide)
    (by simp [a, afterCopy, StackRoutines.copyStacks, h26])
  have he3 := copy_eval b 2 24 (by decide) (by decide) (by decide)
    (by simp [b, a, afterCopy, StackRoutines.copyStacks, h26])
  obtain ⟨nc, hnc, he4⟩ := convertIndex_eval c 12 (by decide) (by decide)
    (by simp [c, b, a, afterCopy, StackRoutines.copyStacks, h12])
    (by simp [c, b, a, afterCopy, StackRoutines.copyStacks, h25])
  have he5 := copy_eval e 3 13 (by decide) (by decide) (by decide)
    (by simp [e, converted, c, b, a, afterCopy, StackRoutines.copyStacks, h26])
  have he6 := Subexp.TupleProgram.pushConst_eval (23 : Fin 48) (0 : Fin 16) false f
  have he7 := Subexp.TupleProgram.pushConst_eval (6 : Fin 48) (0 : Fin 16) false k
  have he := he1.seq (he2.seq ((he3.seq (he4.seq he5)).seq (he6.seq he7)))
  change Eval prepare _ d z at he
  refine ⟨_, ?_, z, he, ?_⟩
  · have hc24 : c.stacks 24 = d.stacks 2 := by
      simp [c, b, a, afterCopy, StackRoutines.copyStacks, h24]
    rw [hc24] at hnc
    simp [e, converted, c, b, a, afterCopy, StackRoutines.copyStacks, h24, prepareBudget]
    omega
  · funext i
    by_cases hi : i ∈ ([6,7,8,12,13,23,24] : List (Fin 48))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [z, k, f, e, c, b, a, converted,
        afterCopy, StackRoutines.copyStacks, preparedStacks,
        h6, h7, h8, h13, h23, h24]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      rcases hi with ⟨hi6, hi7, hi8, hi12, hi13, hi23, hi24⟩
      simp [z, k, f, e, c, b, a, converted,
        afterCopy, StackRoutines.copyStacks, preparedStacks,
        hi6, hi7, hi8, hi12, hi13, hi23, hi24, h6, h7, h8, h13, h23, h24]

theorem reverseRecords_eval (d : Data) (records : List (List Bool))
    (h6 : d.stacks 6 = [false]) (h23 : d.stacks 23 = Encoding.encodeList id records)
    (h28 : d.stacks 28 = []) :
    ∃ n ≤ 10 * (Encoding.encodeList id records).length, ∃ regs : Fin 16 → Bool,
      Eval reverseRecords n d
        ⟨regs, Function.update (Function.update d.stacks 23 []) 6
          (Encoding.encodeList id records.reverse)⟩ := by
  let small := SubexpNormalizeProgram.filterState false true false [] (d.stacks 27)
    (Encoding.encodeList id records.reverse) []
  have hstart : projectState registers3 reversePorts d =
      SubexpNormalizeProgram.filterState (d.regs 0) (d.regs 1) (d.regs 2)
        (Encoding.encodeList id records) (d.stacks 27) [false] [] := by
    apply state_ext
    · funext i
      fin_cases i <;> simp [projectState, registers3, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.triple]
    · funext i
      fin_cases i <;> simp [projectState, reversePorts, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.quadruple, h6, h23, h28]
  obtain ⟨n, hn, ht⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records [] [] (d.stacks 27)
    (d.regs 0) (d.regs 1) (d.regs 2)
  have ht' : Trace SubexpNormalizeProgram.reverseRecordsProgram n
      ((projectState registers3 reversePorts d).withPC
        (some SubexpNormalizeProgram.reverseRecordsProgram.entry)) (small.withPC none) := by
    simpa only [hstart, small, List.append_nil, Encoding.encodeList] using ht
  have he := eval_call_from_state SubexpNormalizeProgram.reverseRecordsProgram registers3 reversePorts d
    registers3_injective reversePorts_injective ht'
  let e := embedState registers3 reversePorts d small
  have hs : e.stacks = Function.update (Function.update d.stacks 23 []) 6
      (Encoding.encodeList id records.reverse) := by
    funext i
    by_cases hi : ∃ j, reversePorts j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [show e.stacks (reversePorts j) = small.stacks j from
        embedState_stack registers3 reversePorts d small reversePorts_injective j]
      fin_cases j <;> simp [small, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.quadruple, reversePorts, h28]
    · have hi23 : i ≠ 23 := fun h => hi ⟨0, by simpa [reversePorts] using h.symm⟩
      have hi6 : i ≠ 6 := fun h => hi ⟨2, by simpa [reversePorts] using h.symm⟩
      simpa [e, hi23, hi6] using embedState_stack_frame registers3 reversePorts d small i hi
  have heq : e = ⟨e.regs, Function.update (Function.update d.stacks 23 []) 6
      (Encoding.encodeList id records.reverse)⟩ := state_ext rfl hs
  change Eval reverseRecords n d e at he
  rw [heq] at he
  exact ⟨n, hn, e.regs, he⟩

def finishedStacks (d : Data) (records : List (List Bool)) : Fin 48 → List Bool :=
  Function.update (Function.update (Function.update
    (Function.update (Function.update d.stacks 23 []) 6 (Encoding.encodeList id records.reverse))
      7 []) 12 []) 13 []

theorem finish_eval (d : Data) (records : List (List Bool))
    (h6 : d.stacks 6 = [false]) (h23 : d.stacks 23 = Encoding.encodeList id records)
    (h28 : d.stacks 28 = []) :
    ∃ n ≤ 10 * (Encoding.encodeList id records).length +
      2 * (d.stacks 7).length + 2 * (d.stacks 12).length + 2 * (d.stacks 13).length + 25,
      Eval finish n d ⟨fun _ => false, finishedStacks d records⟩ := by
  obtain ⟨nr, hnr, regs, hr⟩ := reverseRecords_eval d records h6 h23 h28
  let a : Data := ⟨regs, Function.update (Function.update d.stacks 23 []) 6
    (Encoding.encodeList id records.reverse)⟩
  let b := cleared a 7
  let c := cleared b 12
  let e := cleared c 13
  have h1 := clear_eval a 7
  have h2 := clear_eval b 12
  have h3 := clear_eval c 13
  have h4 := RegisterResetProgram.all_eval e
  have he := hr.seq (h1.seq (h2.seq (h3.seq h4)))
  change Eval finish _ d ⟨fun _ => false, finishedStacks d records⟩ at he
  refine ⟨_, ?_, he⟩
  simp [a, b, c, cleared]
  omega

end SubexponentialSAT.SubexpFactorRoutingSetup

end OAI.Algorithms
