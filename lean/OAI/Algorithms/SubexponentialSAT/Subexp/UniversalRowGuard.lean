import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSunflowerProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.UnaryCompare
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Count the actual mismatch-index records and compare their count with R. -/

namespace SubexponentialSAT.Subexp.UniversalRowGuard

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 8 32
abbrev Word := List Bool

def countRegs : Fin 2 → Fin 8 := Fin.castAdd 6
def countStacks : Fin 2 → Fin 32 := ![17, 14]
theorem countRegs_injective : Function.Injective countRegs := Fin.castAdd_injective 2 6
theorem countStacks_injective : Function.Injective countStacks := by decide

abbrev count : Cmd 8 32 := .call (ProgramLinking.liftProgram
  SubexpSunflowerProgram.CountRecords.program countRegs countStacks)

def counted (a : Data) (n : ℕ) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update a.stacks 17 []) 14 (Encoding.encodeNat n)⟩

theorem count_eval (records : List Word) (a : Data)
    (hs : a.stacks 17 = Encoding.encodeList id records) (ho : a.stacks 14 = []) :
    Eval count (SubexpSunflowerProgram.CountRecords.steps records) a (counted a records.length) := by
  let inner : State 2 2 := ⟨a.regs ∘ countRegs, a.stacks ∘ countStacks⟩
  let last : State 2 2 := ⟨fun _ => false, ParserProgram.pair [] (Encoding.encodeNat records.length)⟩
  have ht : Trace SubexpSunflowerProgram.CountRecords.program
      (SubexpSunflowerProgram.CountRecords.steps records)
      (inner.withPC (some SubexpSunflowerProgram.CountRecords.program.entry)) (last.withPC none) := by
    have h := SubexpSunflowerProgram.CountRecords.trace records [] [] (inner.regs 0) (inner.regs 1)
    convert h using 1 <;>
      simp [inner, last, SubexpSunflowerProgram.CountRecords.cfg, StructuredProgram.State.withPC,
        countRegs, countStacks  ]
    · constructor <;> funext j <;> fin_cases j <;>
        simp [ParserProgram.pair, hs, ho]
    · funext j
      fin_cases j <;> rfl
  have hin : embedState countRegs countStacks a inner = a := by
    apply embedState_eq_of_ports _ _ _ _ _ countRegs_injective countStacks_injective <;> intros <;> rfl
  have hout : embedState countRegs countStacks a last = counted a records.length := by
    apply embedState_eq_of_ports _ _ _ _ _ countRegs_injective countStacks_injective
    · intro j
      fin_cases j <;> simp [last, counted, countRegs, readRegs]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, h.symm⟩
      simp [counted, readRegs, h0, h1]
    · intro j
      fin_cases j <;> simp [last, counted, countStacks, ParserProgram.pair]
    · intro j hj
      have h17 : j ≠ 17 := fun h => hj ⟨0, h.symm⟩
      have h14 : j ≠ 14 := fun h => hj ⟨1, h.symm⟩
      simp [counted, h17, h14]
  have he := eval_call_lifted SubexpSunflowerProgram.CountRecords.program countRegs countStacks a
    countRegs_injective countStacks_injective (a := inner) (b := last) ht
  simpa only [count, hin, hout] using he

def compareRegs : Fin 4 → Fin 8 := ![0, 1, 2, 7]
def compareStacks : Fin 2 → Fin 32 := ![14, 11]
theorem compareRegs_injective : Function.Injective compareRegs := by decide
theorem compareStacks_injective : Function.Injective compareStacks := by decide

abbrev compare : Cmd 8 32 := .call (ProgramLinking.liftProgram UnaryCompare.program compareRegs compareStacks)

abbrev compareClean : Cmd 8 32 :=
  .seq compare (.seq (.call (clearProgram 14 (0 : Fin 8) 1))
    (.call (clearProgram 11 (0 : Fin 8) 1)))

theorem compareClean_eval (a : Data) :
    ∃ n ≤ 6 * ((a.stacks 14).length + (a.stacks 11).length) + 12, ∃ b : Data,
      Eval compareClean n a b ∧
      b.regs 7 = decide ((a.stacks 14).length ≤ (a.stacks 11).length) ∧
      b.stacks = Function.update (Function.update a.stacks 14 []) 11 [] := by
  let inner : State 4 2 := ⟨a.regs ∘ compareRegs,
    UnaryCompare.pairStacks (a.stacks 14) (a.stacks 11)⟩
  obtain ⟨n, hn, c, ht, hpc, hans⟩ := UnaryCompare.runs inner.regs (a.stacks 14) (a.stacks 11)
  let last : State 4 2 := ⟨c.regs, c.stacks⟩
  have hc : last.withPC none = c := by
    cases c
    simp_all [last, StructuredProgram.State.withPC]
  have ht' : Trace UnaryCompare.program n
      (inner.withPC (some UnaryCompare.program.entry)) (last.withPC none) := by
    rw [hc]
    exact ht
  have hin : embedState compareRegs compareStacks a inner = a := by
    apply embedState_eq_of_ports _ _ _ _ _ compareRegs_injective compareStacks_injective
    · intros; rfl
    · intros; rfl
    · intro j
      fin_cases j <;> simp [inner, UnaryCompare.pairStacks, compareStacks]
    · intros; rfl
  let mid := embedState compareRegs compareStacks a last
  have hcompare : Eval compare n a mid := by
    have he := eval_call_lifted UnaryCompare.program compareRegs compareStacks a
      compareRegs_injective compareStacks_injective (a := inner) (b := last) ht'
    simpa only [compare, hin, mid] using he
  have hanswer : mid.regs 7 = decide ((a.stacks 14).length ≤ (a.stacks 11).length) := by
    change mid.regs (compareRegs 3) = _
    rw [embedState_register _ _ _ _ compareRegs_injective]
    exact hans
  have hl : (mid.stacks 14).length ≤ (a.stacks 14).length := by
    change (mid.stacks (compareStacks 0)).length ≤ _
    rw [embedState_stack _ _ _ _ compareStacks_injective]
    simpa [last, UnaryCompare.start, UnaryCompare.pairStacks] using UnaryCompare.trace_length_le ht 0
  have hr : (mid.stacks 11).length ≤ (a.stacks 11).length := by
    change (mid.stacks (compareStacks 1)).length ≤ _
    rw [embedState_stack _ _ _ _ compareStacks_injective]
    simpa [last, UnaryCompare.start, UnaryCompare.pairStacks] using UnaryCompare.trace_length_le ht 1
  have hframe (j : Fin 32) (h14 : j ≠ 14) (h11 : j ≠ 11) : mid.stacks j = a.stacks j := by
    exact embedState_stack_frame _ _ _ _ j (by
      rintro ⟨k, hk⟩
      fin_cases k <;> simp_all [compareStacks])
  let cleaned : Data := ⟨readRegs mid.regs 0 1 none, clearStacks 14 mid.stacks⟩
  let b : Data := ⟨readRegs cleaned.regs 0 1 none, clearStacks 11 cleaned.stacks⟩
  have h14 := TupleProgram.clear_eval 14 (0 : Fin 8) 1 mid
  have h11 := TupleProgram.clear_eval 11 (0 : Fin 8) 1 cleaned
  refine ⟨n + ((2 * (mid.stacks 14).length + 3) +
    (2 * (cleaned.stacks 11).length + 3)), ?_, b,
      hcompare.seq (h14.seq h11), ?_, ?_⟩
  · have hm := Nat.min_le_left (a.stacks 14).length (a.stacks 11).length
    have hcleaned : cleaned.stacks 11 = mid.stacks 11 := by simp [cleaned, clearStacks]
    rw [hcleaned]
    omega
  · simpa [b, cleaned, readRegs] using hanswer
  · funext j
    by_cases hj14 : j = 14 <;> by_cases hj11 : j = 11
    all_goals simp_all [b, cleaned, clearStacks ]

abbrev command : Cmd 8 32 :=
  .seq (.call (copyProgram 28 17 15 (0 : Fin 8) 1))
    (.seq count (.seq (TupleProgram.pushConst 11 0 false)
      (.seq (.call (copyProgram 13 11 15 (0 : Fin 8) 1)) compareClean)))

theorem command_eval (records : List Word) (limit : Word) (a : Data)
    (hrecords : a.stacks 28 = Encoding.encodeList id records) (hlimit : a.stacks 13 = limit)
    (h11 : a.stacks 11 = []) (h14 : a.stacks 14 = [])
    (h15 : a.stacks 15 = []) (h17 : a.stacks 17 = []) :
    ∃ n ≤ 10 * (Encoding.encodeList id records).length + 13 * limit.length +
        6 * records.length + 40, ∃ b : Data,
      Eval command n a b ∧ b.regs 7 = decide (records.length ≤ limit.length) ∧ b.stacks = a.stacks := by
  let a1 : Data := ⟨readRegs a.regs 0 1 none, copyStacks 28 17 a.stacks⟩
  have hcopy := TupleProgram.copy_eval 28 17 15 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) a h15
  let a2 := counted a1 records.length
  have hcount := count_eval records a1
    (by simp [a1, copyStacks, hrecords, h17]) (by simpa [a1, copyStacks] using h14)
  let a3 := TupleProgram.pushedState (11 : Fin 32) (0 : Fin 8) false a2
  have hpush := TupleProgram.pushConst_eval (11 : Fin 32) (0 : Fin 8) false a2
  let a4 : Data := ⟨readRegs a3.regs 0 1 none, copyStacks 13 11 a3.stacks⟩
  have hlimitCopy := TupleProgram.copy_eval 13 11 15 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) a3
    (by simpa [a3, a2, a1, TupleProgram.pushedState, counted, copyStacks] using h15)
  obtain ⟨nc, hnc, b, hc, hb, hbs⟩ := compareClean_eval a4
  have hs14 : a4.stacks 14 = Encoding.encodeNat records.length := by
    simp [a4, a3, a2, a1, counted, copyStacks]
  have hs11 : a4.stacks 11 = limit ++ [false] := by
    simp [a4, a3, a2, a1, counted, copyStacks, hlimit, h11]
  have ht := hcopy.seq (hcount.seq (hpush.seq (hlimitCopy.seq hc)))
  refine ⟨_, ?_, b, ht, ?_, ?_⟩
  · have hcountBound := SubexpSunflowerProgram.CountRecords.steps_le_encoded records
    have hs13 : a3.stacks 13 = limit := by
      simpa [a3, a2, a1, TupleProgram.pushedState, counted, copyStacks] using hlimit
    simp only [hs14, hs11, Encoding.encodeNat, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil] at hnc
    simp only [hrecords, hs13]
    omega
  · simpa [hs14, hs11, Encoding.encodeNat] using hb
  · rw [hbs]
    funext j
    by_cases hj11 : j = 11 <;> by_cases hj14 : j = 14 <;> by_cases hj17 : j = 17 <;>
      simp_all [a4, a3, a2, a1, TupleProgram.pushedState, counted, copyStacks ]

end SubexponentialSAT.Subexp.UniversalRowGuard

end OAI.Algorithms
