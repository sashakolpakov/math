import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionHashAlphabet
import OAI.Algorithms.SubexponentialSAT.CounterConversions

namespace OAI.Algorithms

/-! Actual preparation of the selector's alphabet and its two unary loop
counters. Input ports0,5,6 hold binary alphabet size, tuple depth and round
count. Port9 is an arbitrary saved row stream; other ports start empty.
The arithmetic that computes these three binary values remains a separate
caller obligation. Their expansion is performed here, with its full cost. -/

namespace SubexponentialSAT.SqrtLog.Execution.HashInputs

open BitProgram StructuredCalls

def firstRegs : Fin 3 → Fin 10 := fun i => ⟨i.val, by omega⟩
def alphabetRegs : Fin 6 → Fin 10 := fun i => ⟨i.val, by omega⟩
def alphabetStacks : Fin 6 → Fin 14 := ![0, 1, 2, 3, 4, 11]

def alphabetPorts : HashAlphabet.Ports 10 14 where
  register := alphabetRegs
  stack := alphabetStacks
  register_injective := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 10 => x.val) h)
  stack_injective := by decide

abbrev depthStacks : Fin 3 → Fin 14 := ![5, 12, 1]
abbrev roundStacks : Fin 3 → Fin 14 := ![6, 13, 1]

abbrev unary (stack : Fin 3 → Fin 14) : Cmd 10 14 :=
  liftCommand CounterConversions.unaryCmd 0 1 firstRegs stack

theorem unary_eval (stack : Fin 3 → Fin 14) (hinj : Function.Injective stack)
    (a : State 10 14) (hout : a.stacks (stack 1) = [])
    (hwork : a.stacks (stack 2) = []) :
    ∃ t ≤ CounterConversions.coreBound (a.stacks (stack 0)) + 1,
      ∃ b : State 10 14, Eval (unary stack) t a b ∧
        b.stacks (stack 0) = [] ∧ b.stacks (stack 2) = [] ∧
        b.stacks (stack 1) = List.replicate (CounterPrograms.value (a.stacks (stack 0))) true ∧
        (∀ i, (∀ j, stack j ≠ i) → b.stacks i = a.stacks i) := by
  let d := projectState firstRegs stack a
  obtain ⟨t, ht, hcost⟩ := CounterConversions.unary_correct d hwork
  let z := CounterConversions.state CounterConversions.zeroRegs []
    (List.replicate (CounterPrograms.value (a.stacks (stack 0))) true)
  have hz : Eval CounterConversions.unaryCmd t d z := by
    simpa only [d, z, projectState, Function.comp_apply, hout, List.append_nil] using ht
  let b := embedState firstRegs stack a z
  have hr : Function.Injective firstRegs := by
    intro i j h; exact Fin.ext (congrArg (fun x : Fin 10 => x.val) h)
  refine ⟨t+1, Nat.add_le_add_right hcost 1, b,
    eval_liftCommand_from_state _ _ _ _ _ _ hr hinj hz, ?_, ?_, ?_, ?_⟩
  · exact embedState_stack _ _ _ _ hinj 0
  · exact embedState_stack _ _ _ _ hinj 2
  · exact embedState_stack _ _ _ _ hinj 1
  · intro i hi
    exact embedState_stack_frame _ _ _ _ i (by rintro ⟨j, hj⟩; exact hi j hj)

abbrev command : Cmd 10 14 :=
  .seq (HashAlphabet.generate alphabetPorts) (.seq (unary depthStacks) (unary roundStacks))

def Ready (a : State 10 14) : Prop :=
  ∀ i : Fin 14, i ≠ 0 → i ≠ 5 → i ≠ 6 → i ≠ 9 → a.stacks i = []

def budget (count depth rounds : List Bool) : ℕ :=
  HashAlphabet.budget (CounterPrograms.value count) count.length + 1 +
    (CounterConversions.coreBound depth + 1) + (CounterConversions.coreBound rounds + 1)

theorem command_eval (a : State 10 14) (ready : Ready a) :
    ∃ t ≤ budget (a.stacks 0) (a.stacks 5) (a.stacks 6),
      ∃ b : State 10 14, Eval command t a b ∧
        b.stacks 11 = ProgramEncoding.encodeRecords (SubexpAlphabetProgram.alphabetWords (a.stacks 0)) ∧
        b.stacks 12 = List.replicate (CounterPrograms.value (a.stacks 5)) true ∧
        b.stacks 13 = List.replicate (CounterPrograms.value (a.stacks 6)) true ∧
        b.stacks 9 = a.stacks 9 ∧ b.stacks 10 = [] ∧
        (∀ i : Fin 9, b.stacks (i.castLE (by decide)) = []) := by
  have hstart : ∀ i : Fin 6, i ≠ 0 → a.stacks (alphabetPorts.stack i) = [] := by
    intro i hi
    fin_cases i <;> simp_all [alphabetPorts, alphabetStacks, Ready]
  obtain ⟨t1, ht1, b, hb, halphabet, hclean, hframe, _⟩ :=
    HashAlphabet.generate_eval alphabetPorts a hstart
  have bf (i : Fin 14) (h0 : i ≠ 0) (h1 : i ≠ 1) (h2 : i ≠ 2)
      (h3 : i ≠ 3) (h4 : i ≠ 4) (h11 : i ≠ 11) : b.stacks i = a.stacks i := by
    apply hframe
    intro j
    fin_cases j
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h11.symm
  obtain ⟨t2, ht2, c, hc, hc5, hc1, hc12, cf⟩ :=
    unary_eval depthStacks (by decide) b
      (by change b.stacks 12 = []
          rw [bf 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact ready 12 (by decide) (by decide) (by decide) (by decide))
      (hclean 1 (by decide))
  have cf' (i : Fin 14) (h5 : i ≠ 5) (h12 : i ≠ 12) (h1 : i ≠ 1) :
      c.stacks i = b.stacks i := by
    apply cf
    intro j
    fin_cases j
    · exact h5.symm
    · exact h12.symm
    · exact h1.symm
  obtain ⟨t3, ht3, d, hd, hd6, hd1, hd13, df⟩ :=
    unary_eval roundStacks (by decide) c
      (by change c.stacks 13 = []
          rw [cf' 13 (by decide) (by decide) (by decide),
              bf 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact ready 13 (by decide) (by decide) (by decide) (by decide))
      hc1
  have df' (i : Fin 14) (h6 : i ≠ 6) (h13 : i ≠ 13) (h1 : i ≠ 1) :
      d.stacks i = c.stacks i := by
    apply df
    intro j
    fin_cases j
    · exact h6.symm
    · exact h13.symm
    · exact h1.symm
  have b5 := bf 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have c6 := (cf' 6 (by decide) (by decide) (by decide)).trans
    (bf 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  refine ⟨t1+(t2+t3), ?_, d, hb.seq (hc.seq hd), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change t2 ≤ CounterConversions.coreBound (b.stacks 5) + 1 at ht2
    change t3 ≤ CounterConversions.coreBound (c.stacks 6) + 1 at ht3
    change t1 ≤ HashAlphabet.budget (CounterPrograms.value (a.stacks 0)) (a.stacks 0).length + 1 at ht1
    rw [b5] at ht2
    rw [c6] at ht3
    dsimp [budget]
    omega
  · rw [df' 11 (by decide) (by decide) (by decide), cf' 11 (by decide) (by decide) (by decide)]
    exact halphabet
  · rw [df' 12 (by decide) (by decide) (by decide)]
    simpa [depthStacks, b5] using hc12
  · simpa [roundStacks, c6] using hd13
  · rw [df' 9 (by decide) (by decide) (by decide), cf' 9 (by decide) (by decide) (by decide)]
    exact bf 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [df' 10 (by decide) (by decide) (by decide), cf' 10 (by decide) (by decide) (by decide),
        bf 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ready 10 (by decide) (by decide) (by decide) (by decide)
  · intro i
    fin_cases i
    all_goals first
      | exact hd1
      | exact hd6
      | (rw [df' _ (by decide) (by decide) (by decide)]; exact hc5)
      | (rw [df' _ (by decide) (by decide) (by decide), cf' _ (by decide) (by decide) (by decide)]
         first
         | exact hclean 0 (by decide)
         | exact hclean 2 (by decide)
         | exact hclean 3 (by decide)
         | exact hclean 4 (by decide)
         | (rw [bf _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact ready _ (by decide) (by decide) (by decide) (by decide)))

end SubexponentialSAT.SqrtLog.Execution.HashInputs

end OAI.Algorithms
