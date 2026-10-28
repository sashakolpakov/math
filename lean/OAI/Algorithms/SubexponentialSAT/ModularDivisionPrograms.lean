import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ModularPrograms

namespace OAI.Algorithms

/-!
# A finite binary long-division program

The modulus and dividend are Boolean words stored on stacks. Every routine below
has a fixed finite table, independently of the lengths and values of these words.
-/

namespace SubexponentialSAT.ModularDivisionPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularPrograms
open SubexponentialSAT.ProgramLinking SubexponentialSAT.StackRoutines

private theorem cfg_ext {r s l : ℕ} {a b : Cfg r s l}
    (hp : a.pc = b.pc) (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  simp_all

private theorem embed_ports {s S l : ℕ}
    (port : Fin s → Fin S) (hinj : Function.Injective port)
    (pc : Option (Fin l)) (regs frameRegs : Fin 8 → Bool)
    (localStk : Fin s → List Bool) (frame target : Fin S → List Bool)
    (hport : ∀ i, target (port i) = localStk i)
    (hframe : ∀ i, (¬ ∃ j, port j = i) → target i = frame i) :
    embedCfg id port id none (⟨none, frameRegs, frame⟩ : Cfg 8 S l)
      ⟨pc, regs, localStk⟩ = ⟨pc, regs, target⟩ := by
  apply cfg_ext
  · cases pc <;> rfl
  · simp [embedCfg]
  · funext i
    classical
    by_cases hi : ∃ j, port j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (embedCfg_stack id port id none _ _ hinj j).trans (hport j).symm
    · exact (embedCfg_stack_frame id port id none _ _ i hi).trans (hframe i hi).symm

private theorem sequence_trace {r s l m n k : ℕ}
    (p : Program r s l) (q : Program r s m)
    (ra rb rc : Fin r → Bool) (sa sb sc : Fin s → List Bool)
    (hp : Trace p n ⟨some p.entry, ra, sa⟩ ⟨none, rb, sb⟩)
    (hq : Trace q k ⟨some q.entry, rb, sb⟩ ⟨none, rc, sc⟩) :
    Trace (link p q) (n + k)
      ⟨some (link p q).entry, ra, sa⟩ ⟨none, rc, sc⟩ := by
  exact link_trace p q hp rfl hq

private theorem sequence_runs {r s l m n k : ℕ}
    (p : Program r s l) (q : Program r s m)
    (ra rb rc : Fin r → Bool) (sa sb sc : Fin s → List Bool)
    (hp : RunsIn p n ⟨some p.entry, ra, sa⟩ ⟨none, rb, sb⟩)
    (hq : RunsIn q k ⟨some q.entry, rb, sb⟩ ⟨none, rc, sc⟩) :
    RunsIn (link p q) (n + k)
      ⟨some (link p q).entry, ra, sa⟩ ⟨none, rc, sc⟩ := by
  exact link_runsIn p q hp rfl hq

/-- Ports 5 and 6 hold the preserved modulus and unprocessed dividend.
Ports 1--4 are reusable work stacks. -/
abbrev seven (candidate modulus input work1 work2 work3 work4 : List Bool) :
    Fin 7 → List Bool := ![candidate, work1, work2, work3, work4, modulus, input]

abbrev resting (candidate modulus input : List Bool) : Fin 7 → List Bool :=
  seven candidate modulus input [] [] [] []

@[simp] theorem resting_candidate (candidate modulus input : List Bool) :
    resting candidate modulus input 0 = candidate := rfl

@[simp] theorem resting_input (candidate modulus input : List Bool) :
    resting candidate modulus input 6 = input := rfl

def paddingPorts : Fin 3 → Fin 7 := ![2, 1, 3]
def conditionalPorts : Fin 5 → Fin 7 := ![0, 1, 2, 3, 4]

theorem paddingPorts_injective : Function.Injective paddingPorts := by decide
theorem conditionalPorts_injective : Function.Injective conditionalPorts := by decide

private theorem embed_padding (pc : Option (Fin 5)) (regs frameRegs : Fin 8 → Bool)
    (candidate modulus input shape word output : List Bool) :
    embedCfg id paddingPorts id none
      (⟨none, frameRegs, resting candidate modulus input⟩ : Cfg 8 7 5)
      (paddingCfg pc regs shape word output) =
      ⟨pc, regs, seven candidate modulus input word shape output []⟩ := by
  apply embed_ports paddingPorts paddingPorts_injective
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · rfl
    · exact False.elim (hi ⟨1, rfl⟩)
    · exact False.elim (hi ⟨0, rfl⟩)
    · exact False.elim (hi ⟨2, rfl⟩)
    · rfl
    · rfl
    · rfl

abbrev paddingWideProgram : Program 8 7 5 :=
  liftProgram paddingProgram id paddingPorts

theorem paddingWide_correct (regs : Fin 8 → Bool)
    (candidate modulus input shape word : List Bool)
    (hlen : word.length ≤ shape.length) :
    ∃ finalRegs : Fin 8 → Bool,
      Trace paddingWideProgram (4 * shape.length + 3)
        ⟨some 0, regs, seven candidate modulus input word shape [] []⟩
        ⟨none, finalRegs,
          seven candidate modulus input [] [] (padTo shape word).reverse []⟩ := by
  obtain ⟨finalRegs, ht, _⟩ := padding_correct regs shape word [] hlen
  have hw := liftProgram_trace paddingProgram id paddingPorts
    (⟨none, regs, resting candidate modulus input⟩ : Cfg 8 7 5)
    Function.injective_id paddingPorts_injective ht
  rw [embed_padding, embed_padding] at hw
  exact ⟨finalRegs, by simpa [paddingWideProgram] using hw⟩

private theorem embed_conditional (pc : Option (Fin 31)) (regs frameRegs : Fin 8 → Bool)
    (candidate modulus input left right output : List Bool) :
    embedCfg id conditionalPorts id none
      (⟨none, frameRegs, resting [] modulus input⟩ : Cfg 8 7 31)
      ⟨pc, regs, wideStacks candidate left right output⟩ =
      ⟨pc, regs, seven candidate modulus input right left output []⟩ := by
  apply embed_ports conditionalPorts conditionalPorts_injective
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · exact False.elim (hi ⟨0, rfl⟩)
    · exact False.elim (hi ⟨1, rfl⟩)
    · exact False.elim (hi ⟨2, rfl⟩)
    · exact False.elim (hi ⟨3, rfl⟩)
    · exact False.elim (hi ⟨4, rfl⟩)
    · rfl
    · rfl

abbrev conditionalWideProgram : Program 8 7 31 :=
  liftProgram conditionalSubtractProgram id conditionalPorts

theorem conditionalWide_correct (regs : Fin 8 → Bool) (hzero : regs 0 = false)
    (candidate modulus input padded : List Bool)
    (hlen : candidate.length = padded.length) :
    ∃ finalRegs : Fin 8 → Bool,
      RunsIn conditionalWideProgram (24 * candidate.length + 14)
        ⟨some 0, regs, seven candidate modulus input padded [] [] []⟩
        ⟨none, finalRegs,
          resting (conditionalDifference candidate padded) modulus input⟩ := by
  obtain ⟨finalRegs, ht, _⟩ := conditionalSubtract_correct regs hzero candidate padded hlen
  have hw := liftProgram_runsIn conditionalSubtractProgram id conditionalPorts
    (⟨none, regs, resting [] modulus input⟩ : Cfg 8 7 31)
    Function.injective_id conditionalPorts_injective ht
  rw [embed_conditional, embed_conditional] at hw
  exact ⟨finalRegs, hw⟩

abbrev copyShapeProgram : Program 8 7 8 := copyProgram 0 2 4 1 3
abbrev copyModulusProgram : Program 8 7 8 := copyProgram 5 1 4 1 3
abbrev movePaddingProgram : Program 8 7 4 := transferProgram 3 1 1 3

private theorem copy_shape (candidate modulus input : List Bool) :
    copyStacks (0 : Fin 7) 2 (resting candidate modulus input) =
      seven candidate modulus input [] candidate [] [] := by
  funext i
  fin_cases i <;> simp [copyStacks, resting, seven]

private theorem copy_modulus (candidate modulus input : List Bool) :
    copyStacks (5 : Fin 7) 1 (seven candidate modulus input [] candidate [] []) =
      seven candidate modulus input modulus candidate [] [] := by
  funext i
  fin_cases i <;> simp [copyStacks, seven]

private theorem move_padding (candidate modulus input padded : List Bool) :
    transferStacks (3 : Fin 7) 1 (seven candidate modulus input [] [] padded.reverse []) =
      seven candidate modulus input padded [] [] [] := by
  funext i
  fin_cases i <;> simp [transferStacks, seven]

abbrev preparePaddingProgram : Program 8 7 25 :=
  link (link (link copyShapeProgram copyModulusProgram) paddingWideProgram) movePaddingProgram

theorem preparePadding_correct (regs : Fin 8 → Bool)
    (candidate modulus input : List Bool) (hlen : modulus.length ≤ candidate.length) :
    ∃ finalRegs : Fin 8 → Bool,
      Trace preparePaddingProgram (14 * candidate.length + 7 * modulus.length + 16)
        ⟨some 0, regs, resting candidate modulus input⟩
        ⟨none, finalRegs,
          seven candidate modulus input (padTo candidate modulus) [] [] []⟩ := by
  let r1 := readRegs regs 1 3 none
  have hc1 := copyProgram_trace (0 : Fin 7) 2 4 (1 : Fin 8) 3
    (by decide) (by decide) (by decide) (by decide)
    regs (resting candidate modulus input) (by rfl)
  have hh1 := halt_after_trace copyShapeProgram hc1 (7 : Fin 8) rfl rfl
  have h1 : Trace copyShapeProgram (7 * candidate.length + 5)
      ⟨some 0, regs, resting candidate modulus input⟩
      ⟨none, r1, seven candidate modulus input [] candidate [] []⟩ := by
    simp only [copyResult, copy_shape] at hh1
    simpa [r1, resting, seven, Nat.add_assoc] using hh1
  have hc2 := copyProgram_trace (5 : Fin 7) 1 4 (1 : Fin 8) 3
    (by decide) (by decide) (by decide) (by decide)
    r1 (seven candidate modulus input [] candidate [] []) (by rfl)
  have hh2 := halt_after_trace copyModulusProgram hc2 (7 : Fin 8) rfl rfl
  have h2 : Trace copyModulusProgram (7 * modulus.length + 5)
      ⟨some 0, r1, seven candidate modulus input [] candidate [] []⟩
      ⟨none, r1, seven candidate modulus input modulus candidate [] []⟩ := by
    simp only [copyResult, copy_modulus] at hh2
    simpa [r1, readRegs_reset, seven, Nat.add_assoc] using hh2
  obtain ⟨r2, h3⟩ := paddingWide_correct r1 candidate modulus input candidate modulus hlen
  let r3 := readRegs r2 1 3 none
  have hc4 := transferProgram_trace (3 : Fin 7) 1 (1 : Fin 8) 3
    (by decide) (by decide) r2
    (seven candidate modulus input [] [] (padTo candidate modulus).reverse [])
  have hh4 := halt_after_trace movePaddingProgram hc4 (3 : Fin 4) rfl rfl
  have h4 : Trace movePaddingProgram (3 * candidate.length + 3)
      ⟨some 0, r2, seven candidate modulus input [] [] (padTo candidate modulus).reverse []⟩
      ⟨none, r3, seven candidate modulus input (padTo candidate modulus) [] [] []⟩ := by
    simp only [transferResult, move_padding] at hh4
    simpa [r3, seven, padTo_length, Nat.add_assoc] using hh4
  have h12 := sequence_trace copyShapeProgram copyModulusProgram _ _ _ _ _ _ h1 h2
  have h123 := sequence_trace _ paddingWideProgram _ _ _ _ _ _ h12 h3
  have h1234 := sequence_trace _ movePaddingProgram _ _ _ _ _ _ h123 h4
  refine ⟨r3, ?_⟩
  convert h1234 using 1
  · ring
  · apply cfg_ext
    · congr 1
    · rfl
    · rfl

abbrev resetBorrowProgram : Program 8 7 2 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code := ![.set 0 false 1, .halt]

theorem resetBorrow_correct (regs : Fin 8 → Bool) (stk : Fin 7 → List Bool) :
    Trace resetBorrowProgram 2
      ⟨some 0, regs, stk⟩ ⟨none, Function.update regs 0 false, stk⟩ := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, execInstr, resetBorrowProgram]

abbrev reductionStepProgram : Program 8 7 58 :=
  link (link preparePaddingProgram resetBorrowProgram) conditionalWideProgram

theorem reductionStep_correct (regs : Fin 8 → Bool)
    (candidate modulus input : List Bool) (hlen : modulus.length ≤ candidate.length) :
    ∃ finalRegs : Fin 8 → Bool,
      RunsIn reductionStepProgram (38 * candidate.length + 7 * modulus.length + 32)
        ⟨some 0, regs, resting candidate modulus input⟩
        ⟨none, finalRegs,
          resting (conditionalDifference candidate (padTo candidate modulus)) modulus input⟩ := by
  obtain ⟨r1, h1⟩ := preparePadding_correct regs candidate modulus input hlen
  have h2 := resetBorrow_correct r1
    (seven candidate modulus input (padTo candidate modulus) [] [] [])
  obtain ⟨r3, h3⟩ := conditionalWide_correct (Function.update r1 0 false) (by simp)
    candidate modulus input (padTo candidate modulus) (padTo_length _ _).symm
  have h12 := sequence_trace preparePaddingProgram resetBorrowProgram _ _ _ _ _ _ h1 h2
  have h123 := sequence_runs _ conditionalWideProgram _ _ _ _ _ _
    ⟨_, le_rfl, h12⟩ h3
  refine ⟨r3, ?_⟩
  convert h123 using 1
  · ring
  · apply cfg_ext
    · congr 1
    · rfl
    · rfl

/-- Four control instructions followed by the fixed reduction-step table.
The step table's halt becomes a jump back to the input loop. -/
def divisionLoopProgram : Program 8 7 62 where
  inputStack := 6
  outputStack := 0
  entry := 0
  code := Fin.addCases
    (motive := fun _ : Fin (4 + 58) => Instr 8 7 62)
    (![.pop 6 1 3 1, .branch 3 2 3, .push 0 1 4, .halt] : Fin 4 → Instr 8 7 62)
    (fun pc : Fin 58 =>
      relocateInstr id id (Fin.natAdd 4) (some 0) (reductionStepProgram.code pc))

private theorem loop_step_code :
    CodeEmbedding reductionStepProgram divisionLoopProgram
      id id (Fin.natAdd 4) (some 0) := by
  intro pc
  simp [divisionLoopProgram]

@[simp] theorem loop_code_0 : divisionLoopProgram.code 0 = .pop 6 1 3 1 := rfl
@[simp] theorem loop_code_1 : divisionLoopProgram.code 1 = .branch 3 2 3 := rfl
@[simp] theorem loop_code_2 : divisionLoopProgram.code 2 = .push 0 1 4 := rfl
@[simp] theorem loop_code_3 : divisionLoopProgram.code 3 = .halt := rfl

private theorem update_input (candidate modulus input next : List Bool) :
    Function.update (resting candidate modulus input) 6 next =
      resting candidate modulus next := by
  funext i
  fin_cases i <;> simp [resting, seven]

private theorem update_candidate (candidate modulus input next : List Bool) :
    Function.update (resting candidate modulus input) 0 next =
      resting next modulus input := by
  funext i
  fin_cases i <;> simp [resting, seven]

theorem divisionLoop_head (regs : Fin 8 → Bool)
    (candidate modulus input : List Bool) (b : Bool) :
    Trace divisionLoopProgram 3
      ⟨some 0, regs, resting candidate modulus (b :: input)⟩
      ⟨some 4, readRegs regs 1 3 (some b), resting (b :: candidate) modulus input⟩ := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, execInstr,
    readRegs, update_input, update_candidate, Function.update_apply]

theorem divisionLoop_exit (regs : Fin 8 → Bool) (candidate modulus : List Bool) :
    Trace divisionLoopProgram 3
      ⟨some 0, regs, resting candidate modulus []⟩
      ⟨none, readRegs regs 1 3 none, resting candidate modulus []⟩ := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, execInstr,
    readRegs, update_input, Function.update_apply]

theorem divisionLoop_iteration (regs : Fin 8 → Bool)
    (candidate modulus input : List Bool) (b : Bool)
    (hlen : modulus.length ≤ candidate.length) :
    ∃ finalRegs : Fin 8 → Bool,
      RunsIn divisionLoopProgram (38 * (candidate.length + 1) + 7 * modulus.length + 35)
        ⟨some 0, regs, resting candidate modulus (b :: input)⟩
        ⟨some 0, finalRegs, resting (shiftReduce modulus candidate b) modulus input⟩ := by
  obtain ⟨finalRegs, hrun⟩ := reductionStep_correct
    (readRegs regs 1 3 (some b)) (b :: candidate) modulus input (by simpa using hlen.trans (Nat.le_succ _))
  have hw := relocate_runsIn reductionStepProgram divisionLoopProgram
    id id (Fin.natAdd 4) (some 0)
    (⟨none, regs, resting candidate modulus input⟩ : Cfg 8 7 62)
    Function.injective_id Function.injective_id loop_step_code hrun
  have hw' : RunsIn divisionLoopProgram
      (38 * (candidate.length + 1) + 7 * modulus.length + 32)
      ⟨some 4, readRegs regs 1 3 (some b), resting (b :: candidate) modulus input⟩
      ⟨some 0, finalRegs, resting (shiftReduce modulus candidate b) modulus input⟩ := by
    simpa [embedCfg_id, relabelCfg, relocatePc, shiftReduce, conditionalDifference] using hw
  have hh := divisionLoop_head regs candidate modulus input b
  have ht := (SubexponentialSAT.Computation.RunsIn.trans
    (⟨3, le_rfl, hh⟩ : RunsIn divisionLoopProgram 3 _ _) hw')
  refine ⟨finalRegs, ?_⟩
  convert ht using 1
  omega

/-- The mathematical fold executed by the loop on its MSB-first input stack. -/
def reduceFrom (modulus candidate : List Bool) : List Bool → List Bool
  | [] => candidate
  | b :: bs => reduceFrom modulus (shiftReduce modulus candidate b) bs

theorem reduceFrom_append (modulus candidate xs ys : List Bool) :
    reduceFrom modulus candidate (xs ++ ys) =
      reduceFrom modulus (reduceFrom modulus candidate xs) ys := by
  induction xs generalizing candidate with
  | nil => rfl
  | cons b bs ih => exact ih (shiftReduce modulus candidate b)

theorem reduceFrom_reverse (modulus input : List Bool) :
    reduceFrom modulus (padTo modulus []) input.reverse = reduce modulus input := by
  induction input with
  | nil => rfl
  | cons b bs ih =>
    simp [List.reverse_cons, reduceFrom_append, reduceFrom, reduce, ih]

theorem divisionLoop_correct (regs : Fin 8 → Bool)
    (candidate modulus input : List Bool) (hlen : modulus.length ≤ candidate.length) :
    ∃ finalRegs : Fin 8 → Bool,
      RunsIn divisionLoopProgram
        (50 * (input.length + 1) * (candidate.length + modulus.length + input.length + 1))
        ⟨some 0, regs, resting candidate modulus input⟩
        ⟨none, finalRegs, resting (reduceFrom modulus candidate input) modulus []⟩ := by
  induction input generalizing regs candidate with
  | nil =>
    refine ⟨readRegs regs 1 3 none, 3, ?_, divisionLoop_exit regs candidate modulus⟩
    simp only [List.length_nil]
    omega
  | cons b bs ih =>
    obtain ⟨r1, h1⟩ := divisionLoop_iteration regs candidate modulus bs b hlen
    have hlen' : modulus.length ≤ (shiftReduce modulus candidate b).length := by
      rw [shiftReduce_length]
      omega
    obtain ⟨r2, h2⟩ := ih r1 (shiftReduce modulus candidate b) hlen'
    refine ⟨r2, ?_⟩
    apply (h1.trans h2).mono
    simp only [List.length_cons, shiftReduce_length]
    nlinarith

abbrev copyInitialModulusProgram : Program 8 7 8 := copyProgram 5 2 4 1 3
abbrev moveInitialRemainderProgram : Program 8 7 4 := transferProgram 3 0 1 3
abbrev reverseInputProgram : Program 8 7 10 := reverseProgram 6 1 2 1 3

private theorem copy_initial (modulus input : List Bool) :
    copyStacks (5 : Fin 7) 2 (resting [] modulus input) =
      seven [] modulus input [] modulus [] [] := by
  funext i
  fin_cases i <;> simp [copyStacks, resting, seven]

private theorem move_initial (modulus input : List Bool) :
    transferStacks (3 : Fin 7) 0
      (seven [] modulus input [] [] (padTo modulus []).reverse []) =
      resting (padTo modulus []) modulus input := by
  funext i
  fin_cases i <;> simp [transferStacks, resting, seven]

private theorem reverse_input (candidate modulus input : List Bool) :
    reverseStacks (6 : Fin 7) (resting candidate modulus input) =
      resting candidate modulus input.reverse := by
  funext i
  fin_cases i <;> simp [reverseStacks, resting, seven]

abbrev initializeProgram : Program 8 7 27 :=
  link (link (link copyInitialModulusProgram paddingWideProgram) moveInitialRemainderProgram)
    reverseInputProgram

theorem initialize_correct (regs : Fin 8 → Bool) (modulus input : List Bool) :
    ∃ finalRegs : Fin 8 → Bool,
      Trace initializeProgram (14 * modulus.length + 9 * input.length + 18)
        ⟨some 0, regs, resting [] modulus input⟩
        ⟨none, finalRegs, resting (padTo modulus []) modulus input.reverse⟩ := by
  let r1 := readRegs regs 1 3 none
  have hc1 := copyProgram_trace (5 : Fin 7) 2 4 (1 : Fin 8) 3
    (by decide) (by decide) (by decide) (by decide)
    regs (resting [] modulus input) (by rfl)
  have hh1 := halt_after_trace copyInitialModulusProgram hc1 (7 : Fin 8) rfl rfl
  have h1 : Trace copyInitialModulusProgram (7 * modulus.length + 5)
      ⟨some 0, regs, resting [] modulus input⟩
      ⟨none, r1, seven [] modulus input [] modulus [] []⟩ := by
    simp only [copyResult, copy_initial] at hh1
    simpa [r1, resting, seven, Nat.add_assoc] using hh1
  obtain ⟨r2, h2⟩ := paddingWide_correct r1 [] modulus input modulus [] (by simp)
  let r3 := readRegs r2 1 3 none
  have hc3 := transferProgram_trace (3 : Fin 7) 0 (1 : Fin 8) 3
    (by decide) (by decide) r2 (seven [] modulus input [] [] (padTo modulus []).reverse [])
  have hh3 := halt_after_trace moveInitialRemainderProgram hc3 (3 : Fin 4) rfl rfl
  have h3 : Trace moveInitialRemainderProgram (3 * modulus.length + 3)
      ⟨some 0, r2, seven [] modulus input [] [] (padTo modulus []).reverse []⟩
      ⟨none, r3, resting (padTo modulus []) modulus input⟩ := by
    simp only [transferResult, move_initial] at hh3
    simpa [r3, seven, padTo_length, Nat.add_assoc] using hh3
  have hc4 := reverseProgram_trace (6 : Fin 7) 1 2 (1 : Fin 8) 3
    (by decide) (by decide) (by decide) (by decide)
    r3 (resting (padTo modulus []) modulus input) (by rfl) (by rfl)
  have hh4 := halt_after_trace reverseInputProgram hc4 (9 : Fin 10) rfl rfl
  have h4 : Trace reverseInputProgram (9 * input.length + 7)
      ⟨some 0, r3, resting (padTo modulus []) modulus input⟩
      ⟨none, r3, resting (padTo modulus []) modulus input.reverse⟩ := by
    simp only [reverseResult, reverse_input] at hh4
    simpa [r3, readRegs_reset, resting, seven, Nat.add_assoc] using hh4
  have h12 := sequence_trace copyInitialModulusProgram paddingWideProgram _ _ _ _ _ _ h1 h2
  have h123 := sequence_trace _ moveInitialRemainderProgram _ _ _ _ _ _ h12 h3
  have h1234 := sequence_trace _ reverseInputProgram _ _ _ _ _ _ h123 h4
  refine ⟨r3, ?_⟩
  convert h1234 using 1
  · ring
  · apply cfg_ext
    · congr 1
    · rfl
    · rfl

/-- One fixed finite program computing binary remainder. -/
abbrev remainderProgram : Program 8 7 89 := link initializeProgram divisionLoopProgram

theorem remainder_correct (regs : Fin 8 → Bool) (modulus input : List Bool) :
    ∃ finalRegs : Fin 8 → Bool,
      RunsIn remainderProgram (100 * (modulus.length + input.length + 1) ^ 2)
        ⟨some 0, regs, resting [] modulus input⟩
        ⟨none, finalRegs, resting (reduce modulus input) modulus []⟩ := by
  obtain ⟨r1, h1⟩ := initialize_correct regs modulus input
  obtain ⟨r2, h2⟩ := divisionLoop_correct r1 (padTo modulus []) modulus input.reverse
    (by rw [padTo_length])
  have ht := sequence_runs initializeProgram divisionLoopProgram _ _ _ _ _ _
    ⟨_, le_rfl, h1⟩ h2
  refine ⟨r2, ?_⟩
  have hbound :
      14 * modulus.length + 9 * input.length + 18 +
        50 * (input.reverse.length + 1) *
          ((padTo modulus []).length + modulus.length + input.reverse.length + 1) ≤
        100 * (modulus.length + input.length + 1) ^ 2 := by
    simp only [List.length_reverse, padTo_length]
    nlinarith [Nat.zero_le modulus.length, Nat.zero_le input.length]
  have ht' := ht.mono hbound
  have hstart :
      (⟨some 0, regs, resting [] modulus input⟩ : Cfg 8 7 89) =
        ⟨some (link initializeProgram divisionLoopProgram).entry, regs,
          resting [] modulus input⟩ := by
    apply cfg_ext
    · congr 1
    · rfl
    · rfl
  rw [hstart]
  simpa only [remainderProgram, reduceFrom_reverse] using ht'

theorem remainder_value (regs : Fin 8 → Bool) (modulus input : List Bool)
    (hm : 0 < SubexponentialSAT.BinaryArithmetic.toNat modulus) :
    ∃ finalRegs output,
      RunsIn remainderProgram (100 * (modulus.length + input.length + 1) ^ 2)
        ⟨some 0, regs, resting [] modulus input⟩
        ⟨none, finalRegs, resting output modulus []⟩ ∧
      output.length = modulus.length + input.length ∧
      SubexponentialSAT.BinaryArithmetic.toNat output =
        SubexponentialSAT.BinaryArithmetic.toNat input % SubexponentialSAT.BinaryArithmetic.toNat modulus := by
  obtain ⟨finalRegs, ht⟩ := remainder_correct regs modulus input
  exact ⟨finalRegs, reduce modulus input, ht, reduce_length _ _, reduce_correct _ _ hm⟩

theorem remainder_primitive (regs : Fin 8 → Bool) (modulus input : List Bool) :
    ∃ finalRegs,
      SubexponentialSAT.Computation.RunsIn (primitive remainderProgram).step
        (primitiveOverhead remainderProgram * (100 * (modulus.length + input.length + 1) ^ 2))
        (primitiveCfg remainderProgram ⟨some 0, regs, resting [] modulus input⟩)
        (primitiveCfg remainderProgram
          ⟨none, finalRegs, resting (reduce modulus input) modulus []⟩) := by
  obtain ⟨finalRegs, ht⟩ := remainder_correct regs modulus input
  exact ⟨finalRegs, primitive_execution _ ht⟩

end SubexponentialSAT.ModularDivisionPrograms

end OAI.Algorithms
