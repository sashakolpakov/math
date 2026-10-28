import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpAlphabetProgram
import OAI.Algorithms.SubexponentialSAT.SubexpNodeCost
import OAI.Algorithms.SubexponentialSAT.CounterNormalizeProgram

namespace OAI.Algorithms

/-!
# Fixed-control generation of the selected field's nonzero node table

This program starts with a binary counter, generates its fixed-width scalar
alphabet, and then constructs and filters all four-coordinate words. Its code
contains no precomputed scalar alphabet, field elements, or node table.
-/

namespace SubexponentialSAT.SubexpFieldSetup

open BitProgram StructuredCalls Subexp.TupleProgram
open Subexp.BlockSearchPreparation (restrictState lifted_call)

def alphabetRegisters (i : Fin 6) : Fin 10 := ⟨i.val, by omega⟩
def alphabetStacks : Fin 6 → Fin 9 := ![0, 2, 3, 4, 5, 1]

theorem alphabetRegisters_injective : Function.Injective alphabetRegisters := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 10 => x.val) h)

theorem alphabetStacks_injective : Function.Injective alphabetStacks := by decide

def inputState (word : List Bool) (regs : Fin 10 → Bool) : State 10 9 :=
  ⟨regs, fun i => if i = 0 then word else []⟩

def depthState (a : State 10 9) : State 10 9 :=
  pushedState 8 6 false (pushedState 8 6 false
    (pushedState 8 6 false (pushedState 8 6 false a)))

theorem depthFour_eval (a : State 10 9) :
    Eval SubexpNodeGeneration.depthFour 8 a (depthState a) :=
  (pushConst_eval 8 6 false a).seq
    ((pushConst_eval 8 6 false (pushedState 8 6 false a)).seq
      ((pushConst_eval 8 6 false (pushedState 8 6 false (pushedState 8 6 false a))).seq
        (pushConst_eval 8 6 false
          (pushedState 8 6 false (pushedState 8 6 false (pushedState 8 6 false a))))))

abbrev cmd : Cmd 10 9 :=
  .seq (.call (ProgramLinking.liftProgram SubexpAlphabetProgram.program
      alphabetRegisters alphabetStacks))
    (.seq (.call (StackRoutines.clearProgram 0 6 7))
      (.seq SubexpNodeGeneration.depthFour SubexpNodeGeneration.generateFilter))

def program := StructuredCalls.compiled cmd 0 5

def cost (word : List Bool) : ℕ :=
  (CounterPrograms.value word + 1) * (60 * word.length + 60) +
    (2 * word.length + 3) +
    SubexpNodeGeneration.cost (SubexpAlphabetProgram.alphabetWords word)

/-- The setup trace accounts for both the generated alphabet and its removal
from the spent counter port before the node generator starts. -/
theorem program_runsIn_from (word : List Bool) (regs : Fin 10 → Bool) :
    ∃ next : State 10 9,
      next.stacks 5 = ProgramEncoding.encodeRecords
        (SubexpNodeGeneration.generatedWords (SubexpAlphabetProgram.alphabetWords word)) ∧
      RunsIn program (cost word)
        ((inputState word regs).withPC (some program.entry)) (next.withPC none) := by
  let a := inputState word regs
  obtain ⟨small, hout, hc, hs, _, hw, hr⟩ :=
    SubexpAlphabetProgram.program_runsIn_clean word (regs ∘ alphabetRegisters)
  have hrestrict : restrictState alphabetRegisters alphabetStacks a =
      SubexpAlphabetProgram.inputState word (regs ∘ alphabetRegisters) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [a, inputState, alphabetStacks]
  have hr' : RunsIn SubexpAlphabetProgram.program
      ((CounterPrograms.value word + 1) * (60 * word.length + 60))
      ((restrictState alphabetRegisters alphabetStacks a).withPC
        (some SubexpAlphabetProgram.program.entry)) (small.withPC none) := by
    simpa only [hrestrict] using hr
  obtain ⟨na, hna, hea⟩ := lifted_call SubexpAlphabetProgram.program
    alphabetRegisters alphabetStacks alphabetRegisters_injective alphabetStacks_injective
    a small _ hr'
  let b := embedState alphabetRegisters alphabetStacks a small
  have hb (i : Fin 6) : b.stacks (alphabetStacks i) = small.stacks i :=
    embedState_stack alphabetRegisters alphabetStacks a small alphabetStacks_injective i
  have hb0 : (b.stacks 0).length = word.length := by
    simpa only [alphabetStacks, Matrix.cons_val_zero] using (congrArg List.length (hb 0)).trans hw
  have hb1 : b.stacks 1 = ProgramEncoding.encodeRecords
      (SubexpAlphabetProgram.alphabetWords word) := by
    simpa only [show alphabetStacks 5 = (1 : Fin 9) from rfl] using (hb 5).trans hout
  have hb2 : b.stacks 2 = [] := by
    simpa only [show alphabetStacks 1 = (2 : Fin 9) from rfl] using (hb 1).trans hs
  have hb3 : b.stacks 3 = [] := by
    simpa only [show alphabetStacks 2 = (3 : Fin 9) from rfl] using (hb 2).trans hc.1
  have hb4 : b.stacks 4 = [] := by
    simpa only [show alphabetStacks 3 = (4 : Fin 9) from rfl] using (hb 3).trans hc.2.1
  have hb5 : b.stacks 5 = [] := by
    simpa only [show alphabetStacks 4 = (5 : Fin 9) from rfl] using (hb 4).trans hc.2.2
  have hb6 : b.stacks 6 = [] := by
    exact (embedState_stack_frame alphabetRegisters alphabetStacks a small 6
      (by decide)).trans (by simp [a, inputState])
  have hb7 : b.stacks 7 = [] := by
    exact (embedState_stack_frame alphabetRegisters alphabetStacks a small 7
      (by decide)).trans (by simp [a, inputState])
  have hb8 : b.stacks 8 = [] := by
    exact (embedState_stack_frame alphabetRegisters alphabetStacks a small 8
      (by decide)).trans (by simp [a, inputState])
  let c : State 10 9 :=
    ⟨readRegs b.regs 6 7 none, StackRoutines.clearStacks 0 b.stacks⟩
  let d := depthState c
  have hd : outerInvariant (SubexpAlphabetProgram.alphabetWords word)
      [false, false, false, false] (d.regs 9) d := by
    simp [outerInvariant, d, depthState, c, pushedState, StackRoutines.clearStacks,
      hb1, hb3, hb4, hb6, hb7, hb8]
  have hd0 : d.stacks 0 = [] := by
    simp [d, depthState, c, pushedState, StackRoutines.clearStacks]
  have hd2 : d.stacks 2 = [] := by
    simp [d, depthState, c, pushedState, StackRoutines.clearStacks, hb2]
  have hd5 : d.stacks 5 = [] := by
    simp [d, depthState, c, pushedState, StackRoutines.clearStacks, hb5]
  obtain ⟨nn, next, hnn, hnext, hen⟩ := SubexpNodeGeneration.generateFilter_eval
    (SubexpAlphabetProgram.alphabetWords word) [false, false, false, false]
    (d.regs 9) d hd hd0 hd2 hd5
  refine ⟨next, hnext, na + ((2 * (b.stacks 0).length + 3) + (8 + nn)) + 1, ?_, ?_⟩
  · rw [hb0]
    change nn ≤ powerCost (SubexpAlphabetProgram.alphabetWords word) 4 [[]] +
      SubexpNodeFilter.budget
        (powerRows (SubexpAlphabetProgram.alphabetWords word) 4 [[]]) + 10 at hnn
    unfold cost SubexpNodeGeneration.cost
    omega
  · exact StructuredCalls.compiled_halt_trace
      (hea.seq ((clear_eval 0 6 7 b).seq ((depthFour_eval c).seq hen))) 0 5

theorem program_runsIn (word : List Bool) :
    ∃ next : State 10 9,
      next.stacks 5 = ProgramEncoding.encodeRecords
        (SubexpNodeGeneration.generatedWords (SubexpAlphabetProgram.alphabetWords word)) ∧
      RunsIn program (cost word) (initial program word) (next.withPC none) :=
  program_runsIn_from word (fun _ => false)

theorem generatedWords_primeWord (p : ℕ) [Fact p.Prime] :
    SubexpNodeGeneration.generatedWords
        (SubexpAlphabetProgram.alphabetWords (SubexpAlphabetProgram.primeWord p)) =
      SubexpMachineNodeOrder.nodeWords p := by
  rw [SubexpAlphabetProgram.alphabetWords_primeWord]
  rfl

theorem selected_program_runsIn (p : ℕ) [Fact p.Prime] :
    ∃ next : State 10 9,
      next.stacks 5 = ProgramEncoding.encodeRecords (SubexpMachineNodeOrder.nodeWords p) ∧
      RunsIn program (cost (SubexpAlphabetProgram.primeWord p))
        (initial program (SubexpAlphabetProgram.primeWord p)) (next.withPC none) := by
  simpa only [generatedWords_primeWord] using
    program_runsIn (SubexpAlphabetProgram.primeWord p)

/-- Polynomial cost for the actual complete enumeration, including building
the input alphabet. The only unbounded data are the counter word and buffers. -/
theorem cost_le (word : List Bool) :
    cost word ≤ 1100 * (CounterPrograms.value word + 1) ^ 4 * (word.length + 1) := by
  have hn := SubexpNodeCost.cost_le (SubexpAlphabetProgram.alphabetWords word)
    word.length (by
      intro w hw
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hw
      exact le_of_eq (SubexpLiftRing.fixedBits_length _ _))
  simp only [SubexpAlphabetProgram.alphabetWords, List.length_map, List.length_range] at hn
  change SubexpNodeGeneration.cost (SubexpAlphabetProgram.alphabetWords word) ≤
    1000 * (CounterPrograms.value word + 1) ^ 4 * (word.length + 1) at hn
  have hp : CounterPrograms.value word + 1 ≤ (CounterPrograms.value word + 1) ^ 4 :=
    Nat.le_pow (by decide)
  have hm := Nat.mul_le_mul_right (word.length + 1) hp
  have hq : 1 ≤ (CounterPrograms.value word + 1) ^ 4 := by omega
  have hs := Nat.mul_le_mul_right (word.length + 1) hq
  simp only [one_mul] at hs
  have ha : (CounterPrograms.value word + 1) * (60 * word.length + 60) ≤
      60 * ((CounterPrograms.value word + 1) ^ 4 * (word.length + 1)) := by
    calc
      _ = 60 * ((CounterPrograms.value word + 1) * (word.length + 1)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left 60 hm
  have hc : 2 * word.length + 3 ≤
      3 * ((CounterPrograms.value word + 1) ^ 4 * (word.length + 1)) := by omega
  unfold cost
  nlinarith

theorem primitive_runsIn (word : List Bool) :
    ∃ next : State 10 9,
      next.stacks 5 = ProgramEncoding.encodeRecords
        (SubexpNodeGeneration.generatedWords (SubexpAlphabetProgram.alphabetWords word)) ∧
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * cost word)
        (primitiveCfg program (initial program word)) (primitiveCfg program (next.withPC none)) := by
  obtain ⟨next, hout, hr⟩ := program_runsIn word
  exact ⟨next, hout, primitive_execution program hr⟩

def normalizeRegisters (i : Fin 3) : Fin 10 := ⟨i.val, by omega⟩
def normalizeStacks (i : Fin 3) : Fin 9 := ⟨i.val, by omega⟩

theorem normalizeRegisters_injective : Function.Injective normalizeRegisters := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 10 => x.val) h)

theorem normalizeStacks_injective : Function.Injective normalizeStacks := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 9 => x.val) h)

abbrev normalizedCmd : Cmd 10 9 :=
  .seq (.call (ProgramLinking.liftProgram CounterNormalizeProgram.program
    normalizeRegisters normalizeStacks)) (.call program)

def normalizedProgram := StructuredCalls.compiled normalizedCmd 0 5

def normalizedCost (word : List Bool) : ℕ :=
  9 * word.length + 21 +
    cost (SubexpAlphabetProgram.primeWord (CounterPrograms.value word)) + 1

/-- The front end accepts high zero padding. An actual normalization program
removes that padding before the alphabet determines the coefficient width. -/
theorem normalized_program_runsIn_from (word : List Bool) (regs : Fin 10 → Bool)
    (hp : 0 < CounterPrograms.value word) :
    ∃ next : State 10 9,
      next.stacks 5 = ProgramEncoding.encodeRecords
        (SubexpNodeGeneration.generatedWords (SubexpAlphabetProgram.alphabetWords
          (SubexpAlphabetProgram.primeWord (CounterPrograms.value word)))) ∧
      RunsIn normalizedProgram (normalizedCost word)
        ((inputState word regs).withPC (some normalizedProgram.entry))
        (next.withPC none) := by
  let a := inputState word regs
  let canonical := SubexpAlphabetProgram.primeWord (CounterPrograms.value word)
  let small := CounterNormalizeProgram.state CounterNormalizeProgram.zeroRegs canonical []
  have hrestrict : restrictState normalizeRegisters normalizeStacks a =
      CounterNormalizeProgram.state (regs ∘ normalizeRegisters) word [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [a, inputState, normalizeStacks]
  have hr : RunsIn CounterNormalizeProgram.program (9 * word.length + 21)
      ((restrictState normalizeRegisters normalizeStacks a).withPC
        (some CounterNormalizeProgram.program.entry)) (small.withPC none) := by
    simpa only [hrestrict, small, canonical, SubexpAlphabetProgram.primeWord,
      SubexpEnumerationPayload.scalarWidth, Nat.log2_eq_log_two] using
      CounterNormalizeProgram.normalize_runs (regs ∘ normalizeRegisters) word hp
  obtain ⟨nn, hnn, hen⟩ := lifted_call CounterNormalizeProgram.program
    normalizeRegisters normalizeStacks normalizeRegisters_injective normalizeStacks_injective
    a small _ hr
  let b := embedState normalizeRegisters normalizeStacks a small
  have hb (i : Fin 3) : b.stacks (normalizeStacks i) = small.stacks i :=
    embedState_stack normalizeRegisters normalizeStacks a small normalizeStacks_injective i
  have hbf (i : Fin 9) (hi : ¬ ∃ j, normalizeStacks j = i) :
      b.stacks i = a.stacks i :=
    embedState_stack_frame normalizeRegisters normalizeStacks a small i hi
  have hbstate : b = inputState canonical b.regs := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i
      · have h := hb 0
        change b.stacks 0 = canonical at h
        exact h
      · have h := hb 1
        change b.stacks 1 = [] at h
        exact h
      · have h := hb 2
        change b.stacks 2 = [] at h
        exact h
      all_goals exact (hbf _ (by decide)).trans (by simp [a, inputState])
  obtain ⟨next, hout, nf, hnf, hef⟩ := program_runsIn_from canonical b.regs
  rw [← hbstate] at hef
  dsimp only [canonical] at hnf
  refine ⟨next, hout, nn + nf + 1, by unfold normalizedCost; omega, ?_⟩
  exact StructuredCalls.compiled_halt_trace (hen.seq (Eval.call _ hef)) 0 5

theorem normalized_program_runsIn (word : List Bool) (hp : 0 < CounterPrograms.value word) :
    ∃ next : State 10 9,
      next.stacks 5 = ProgramEncoding.encodeRecords
        (SubexpNodeGeneration.generatedWords (SubexpAlphabetProgram.alphabetWords
          (SubexpAlphabetProgram.primeWord (CounterPrograms.value word)))) ∧
      RunsIn normalizedProgram (normalizedCost word)
        (initial normalizedProgram word) (next.withPC none) :=
  normalized_program_runsIn_from word (fun _ => false) hp

/-- The exact node-list order is the order consumed by the selected-field
layout, and follows the actual tuple and record-filter programs. -/
theorem selected_normalized_program_runsIn (p : ℕ) [Fact p.Prime]
    (word : List Bool) (hv : CounterPrograms.value word = p) :
    ∃ next : State 10 9,
      next.stacks 5 = ProgramEncoding.encodeRecords (SubexpMachineNodeOrder.nodeWords p) ∧
      RunsIn normalizedProgram (normalizedCost word)
        (initial normalizedProgram word) (next.withPC none) := by
  have hp : 0 < CounterPrograms.value word := by
    rw [hv]
    exact (Fact.out : p.Prime).pos
  simpa only [hv, generatedWords_primeWord] using
    normalized_program_runsIn word hp

theorem normalizedCost_le (word : List Bool) (hp : 0 < CounterPrograms.value word) :
    normalizedCost word ≤
      1200 * (CounterPrograms.value word + 1) ^ 4 * (word.length + 1) := by
  have hl : Nat.log2 (CounterPrograms.value word) < word.length :=
    (Nat.log2_lt (ne_of_gt hp)).mpr (SubexpParameterProgram.value_lt_two_pow_length word)
  have hc := cost_le (SubexpAlphabetProgram.primeWord (CounterPrograms.value word))
  simp only [SubexpAlphabetProgram.primeWord_value, SubexpAlphabetProgram.primeWord_length,
    SubexpEnumerationPayload.scalarWidth, ← Nat.log2_eq_log_two] at hc
  have hw : Nat.log2 (CounterPrograms.value word) + 1 + 1 ≤ word.length + 1 := by omega
  have hm := Nat.mul_le_mul_left (1100 * (CounterPrograms.value word + 1) ^ 4) hw
  have hq : 1 ≤ (CounterPrograms.value word + 1) ^ 4 :=
    Nat.succ_le_of_lt (pow_pos (Nat.succ_pos _) 4)
  have hs := Nat.mul_le_mul_right (word.length + 1) hq
  simp only [one_mul] at hs
  unfold normalizedCost
  nlinarith

theorem normalized_primitive_runsIn (word : List Bool)
    (hp : 0 < CounterPrograms.value word) :
    ∃ next : State 10 9,
      next.stacks 5 = ProgramEncoding.encodeRecords
        (SubexpNodeGeneration.generatedWords (SubexpAlphabetProgram.alphabetWords
          (SubexpAlphabetProgram.primeWord (CounterPrograms.value word)))) ∧
      Computation.RunsIn (primitive normalizedProgram).step
        (primitiveOverhead normalizedProgram * normalizedCost word)
        (primitiveCfg normalizedProgram (initial normalizedProgram word))
        (primitiveCfg normalizedProgram (next.withPC none)) := by
  obtain ⟨next, hout, hr⟩ := normalized_program_runsIn word hp
  exact ⟨next, hout, primitive_execution normalizedProgram hr⟩

/-- Prepared-state interface for relocation into the complete setup program. -/
theorem selected_normalized_program_runsIn_from (p : ℕ) [Fact p.Prime]
    (word : List Bool) (hv : CounterPrograms.value word = p) (regs : Fin 10 → Bool) :
    ∃ next : State 10 9,
      next.stacks 5 = ProgramEncoding.encodeRecords (SubexpMachineNodeOrder.nodeWords p) ∧
      RunsIn normalizedProgram (1200 * (p + 1) ^ 4 * (word.length + 1))
        ((inputState word regs).withPC (some normalizedProgram.entry))
        (next.withPC none) := by
  have hp : 0 < CounterPrograms.value word := by
    rw [hv]
    exact (Fact.out : p.Prime).pos
  obtain ⟨next, hout, hr⟩ := normalized_program_runsIn_from word regs hp
  refine ⟨next, ?_, hr.mono ?_⟩
  · simpa only [hv, generatedWords_primeWord] using hout
  · simpa only [hv] using normalizedCost_le word hp

theorem selected_normalized_primitive_runsIn (p : ℕ) [Fact p.Prime]
    (word : List Bool) (hv : CounterPrograms.value word = p) :
    ∃ next : State 10 9,
      next.stacks 5 = ProgramEncoding.encodeRecords (SubexpMachineNodeOrder.nodeWords p) ∧
      Computation.RunsIn (primitive normalizedProgram).step
        (primitiveOverhead normalizedProgram * (1200 * (p + 1) ^ 4 * (word.length + 1)))
        (primitiveCfg normalizedProgram (initial normalizedProgram word))
        (primitiveCfg normalizedProgram (next.withPC none)) := by
  obtain ⟨next, hout, hr⟩ := selected_normalized_program_runsIn_from p word hv (fun _ => false)
  exact ⟨next, hout, primitive_execution normalizedProgram hr⟩

end SubexponentialSAT.SubexpFieldSetup

end OAI.Algorithms
