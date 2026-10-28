import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ModularDivisionPrograms
import OAI.Algorithms.SubexponentialSAT.ModularQuotientArithmetic

namespace OAI.Algorithms

/-! Binary quotient and remainder from a fixed finite Boolean-stack program. -/

namespace SubexponentialSAT.ModularQuotientPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.ProgramLinking SubexponentialSAT.StackRoutines
open SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularPrograms SubexponentialSAT.ModularDivisionPrograms
open SubexponentialSAT.ModularQuotientArithmetic

private theorem cfg_ext {r s l : ℕ} {a b : Cfg r s l}
    (hp : a.pc = b.pc) (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  simp_all

private theorem embed_ports {s S l L : ℕ}
    (port : Fin s → Fin S) (hinj : Function.Injective port)
    (label : Fin l → Fin L) (ret : Option (Fin L))
    (pc : Option (Fin l)) (regs frameRegs : Fin 8 → Bool)
    (localStk : Fin s → List Bool) (frame target : Fin S → List Bool)
    (hport : ∀ i, target (port i) = localStk i)
    (hframe : ∀ i, (¬ ∃ j, port j = i) → target i = frame i) :
    embedCfg id port label ret (⟨none, frameRegs, frame⟩ : Cfg 8 S L)
      ⟨pc, regs, localStk⟩ = ⟨relocatePc label ret pc, regs, target⟩ := by
  apply cfg_ext
  · rfl
  · simp [embedCfg]
  · funext i
    classical
    by_cases hi : ∃ j, port j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (embedCfg_stack id port label ret _ _ hinj j).trans (hport j).symm
    · exact (embedCfg_stack_frame id port label ret _ _ i hi).trans (hframe i hi).symm

private theorem embed_conditional (pc : Option (Fin 31)) (regs frameRegs : Fin 8 → Bool)
    (candidate modulus input left right output : List Bool) :
    embedCfg id conditionalPorts id none
      (⟨none, frameRegs, resting [] modulus input⟩ : Cfg 8 7 31)
      ⟨pc, regs, wideStacks candidate left right output⟩ =
      ⟨pc, regs, seven candidate modulus input right left output []⟩ := by
  have he :
      embedCfg id conditionalPorts id none
        (⟨none, frameRegs, resting [] modulus input⟩ : Cfg 8 7 31)
        ⟨pc, regs, wideStacks candidate left right output⟩ =
        ⟨relocatePc id none pc, regs, seven candidate modulus input right left output []⟩ := by
    apply embed_ports conditionalPorts conditionalPorts_injective
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i
      · exact False.elim (hi ⟨0, rfl⟩)
      · exact False.elim (hi ⟨1, rfl⟩)
      · exact False.elim (hi ⟨2, rfl⟩)
      · exact False.elim (hi ⟨3, rfl⟩)
      · exact False.elim (hi ⟨4, rfl⟩)
      · rfl
      · rfl
  cases pc <;> exact he

theorem conditional_borrow (regs : Fin 8 → Bool) (hzero : regs 0 = false)
    (candidate modulus input padded : List Bool)
    (hlen : candidate.length = padded.length) :
    ∃ finalRegs,
      RunsIn conditionalWideProgram (24 * candidate.length + 14)
        ⟨some 0, regs, seven candidate modulus input padded [] [] []⟩
        ⟨none, finalRegs,
          resting (conditionalDifference candidate padded) modulus input⟩ ∧
      finalRegs 0 = (subCarry false candidate padded).2 := by
  obtain ⟨rf, hr, hb⟩ := conditionalSubtract_correct regs hzero candidate padded hlen
  have hw := liftProgram_runsIn conditionalSubtractProgram id conditionalPorts
    (⟨none, regs, resting [] modulus input⟩ : Cfg 8 7 31)
    Function.injective_id conditionalPorts_injective hr
  rw [embed_conditional, embed_conditional] at hw
  exact ⟨rf, hw, hb⟩

theorem reductionStep_borrow (regs : Fin 8 → Bool)
    (candidate modulus input : List Bool) (hlen : modulus.length ≤ candidate.length) :
    ∃ finalRegs,
      RunsIn reductionStepProgram (38 * candidate.length + 7 * modulus.length + 32)
        ⟨some 0, regs, resting candidate modulus input⟩
        ⟨none, finalRegs,
          resting (conditionalDifference candidate (padTo candidate modulus)) modulus input⟩ ∧
      finalRegs 0 = (subCarry false candidate (padTo candidate modulus)).2 := by
  obtain ⟨r1, h1⟩ := preparePadding_correct regs candidate modulus input hlen
  have h2 := resetBorrow_correct r1
    (seven candidate modulus input (padTo candidate modulus) [] [] [])
  obtain ⟨rf, h3, hb⟩ := conditional_borrow (Function.update r1 0 false) (by simp)
    candidate modulus input (padTo candidate modulus) (padTo_length _ _).symm
  have h12 := link_trace preparePaddingProgram resetBorrowProgram h1 rfl h2
  have h123 := link_runsIn (link preparePaddingProgram resetBorrowProgram)
    conditionalWideProgram ⟨_, le_rfl, h12⟩ rfl h3
  refine ⟨rf, ?_, hb⟩
  convert h123 using 1
  all_goals try omega
  all_goals
    apply cfg_ext
    · simp [ relocatePc
         ]
    · rfl
    · rfl

abbrev quotientStacks (remainder modulus input quotient : List Bool) : Fin 8 → List Bool :=
  ![remainder, [], [], [], [], modulus, input, quotient]

def quotientPorts : Fin 7 → Fin 8 := ![0, 1, 2, 3, 4, 5, 6]
theorem quotientPorts_injective : Function.Injective quotientPorts := by decide

private theorem embed_quotient {l L : ℕ} (label : Fin l → Fin L) (ret : Option (Fin L))
    (pc : Option (Fin l)) (regs frameRegs : Fin 8 → Bool)
    (remainder modulus input quotient : List Bool) :
    embedCfg id quotientPorts label ret
      (⟨none, frameRegs, quotientStacks [] [] [] quotient⟩ : Cfg 8 8 L)
      ⟨pc, regs, resting remainder modulus input⟩ =
      ⟨relocatePc label ret pc, regs, quotientStacks remainder modulus input quotient⟩ := by
  apply embed_ports quotientPorts quotientPorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · exact False.elim (hi ⟨0, rfl⟩)
    · exact False.elim (hi ⟨1, rfl⟩)
    · exact False.elim (hi ⟨2, rfl⟩)
    · exact False.elim (hi ⟨3, rfl⟩)
    · exact False.elim (hi ⟨4, rfl⟩)
    · exact False.elim (hi ⟨5, rfl⟩)
    · exact False.elim (hi ⟨6, rfl⟩)
    · rfl

def stepLabel (pc : Fin 58) : Fin 65 := Fin.natAdd 4 (Fin.castAdd 3 pc)

def quotientLoopProgram : Program 8 8 65 where
  inputStack := 6
  outputStack := 7
  entry := 0
  code := Fin.addCases
    (motive := fun _ : Fin (4 + (58 + 3)) => Instr 8 8 65)
    (![.pop 6 1 3 1, .branch 3 2 3, .push 0 1 4, .halt] : Fin 4 → Instr 8 8 65)
    (Fin.addCases
      (motive := fun _ : Fin (58 + 3) => Instr 8 8 65)
      (fun pc : Fin 58 =>
        relocateInstr id quotientPorts stepLabel (some 62) (reductionStepProgram.code pc))
      (![.bnot 0 0 63, .push 7 0 64, .goto 0] : Fin 3 → Instr 8 8 65))

@[simp] theorem quotientLoop_entry : quotientLoopProgram.entry = 0 := rfl

private theorem quotient_step_code :
    CodeEmbedding reductionStepProgram quotientLoopProgram
      id quotientPorts stepLabel (some 62) := by
  intro pc
  simp [quotientLoopProgram, stepLabel]

@[simp] theorem quotient_code_0 : quotientLoopProgram.code 0 = .pop 6 1 3 1 := rfl
@[simp] theorem quotient_code_1 : quotientLoopProgram.code 1 = .branch 3 2 3 := rfl
@[simp] theorem quotient_code_2 : quotientLoopProgram.code 2 = .push 0 1 4 := rfl
@[simp] theorem quotient_code_3 : quotientLoopProgram.code 3 = .halt := rfl
@[simp] theorem quotient_code_62 : quotientLoopProgram.code 62 = .bnot 0 0 63 := rfl
@[simp] theorem quotient_code_63 : quotientLoopProgram.code 63 = .push 7 0 64 := rfl
@[simp] theorem quotient_code_64 : quotientLoopProgram.code 64 = .goto 0 := rfl

@[simp] theorem quotient_stack_0 (r m x q : List Bool) : quotientStacks r m x q 0 = r := rfl
@[simp] theorem quotient_stack_6 (r m x q : List Bool) : quotientStacks r m x q 6 = x := rfl
@[simp] theorem quotient_stack_7 (r m x q : List Bool) : quotientStacks r m x q 7 = q := rfl

private theorem update_remainder (r m x q next : List Bool) :
    Function.update (quotientStacks r m x q) 0 next = quotientStacks next m x q := by
  funext i; fin_cases i <;> simp [quotientStacks]

private theorem update_dividend (r m x q next : List Bool) :
    Function.update (quotientStacks r m x q) 6 next = quotientStacks r m next q := by
  funext i; fin_cases i <;> simp [quotientStacks]

private theorem update_quotient (r m x q next : List Bool) :
    Function.update (quotientStacks r m x q) 7 next = quotientStacks r m x next := by
  funext i; fin_cases i <;> simp [quotientStacks]

theorem quotientLoop_head (regs : Fin 8 → Bool) (r m x q : List Bool) (b : Bool) :
    Trace quotientLoopProgram 3
      ⟨some 0, regs, quotientStacks r m (b :: x) q⟩
      ⟨some 4, readRegs regs 1 3 (some b), quotientStacks (b :: r) m x q⟩ := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, execInstr, readRegs,
    update_remainder, update_dividend, Function.update_apply]

theorem quotientLoop_digit (regs : Fin 8 → Bool) (r m x q : List Bool) :
    Trace quotientLoopProgram 3
      ⟨some 62, regs, quotientStacks r m x q⟩
      ⟨some 0, Function.update regs 0 (!(regs 0)), quotientStacks r m x ((!(regs 0)) :: q)⟩ := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, execInstr, update_quotient]

theorem quotientLoop_exit (regs : Fin 8 → Bool) (r m q : List Bool) :
    Trace quotientLoopProgram 3
      ⟨some 0, regs, quotientStacks r m [] q⟩
      ⟨none, readRegs regs 1 3 none, quotientStacks r m [] q⟩ := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, execInstr, readRegs,
    update_dividend, Function.update_apply]

theorem quotientLoop_iteration (regs : Fin 8 → Bool)
    (r m x q : List Bool) (b : Bool) (hlen : m.length ≤ r.length) :
    ∃ finalRegs,
      RunsIn quotientLoopProgram (38 * (r.length + 1) + 7 * m.length + 38)
        ⟨some 0, regs, quotientStacks r m (b :: x) q⟩
        ⟨some 0, finalRegs,
          quotientStacks (shiftReduce m r b) m x (quotientBit m r b :: q)⟩ := by
  obtain ⟨rf, hr, hb⟩ := reductionStep_borrow (readRegs regs 1 3 (some b))
    (b :: r) m x (by simpa using hlen.trans (Nat.le_succ _))
  have hw := relocate_runsIn reductionStepProgram quotientLoopProgram
    id quotientPorts stepLabel (some 62)
    (⟨none, regs, quotientStacks [] [] [] q⟩ : Cfg 8 8 65)
    Function.injective_id quotientPorts_injective quotient_step_code hr
  rw [embed_quotient, embed_quotient] at hw
  have hw' : RunsIn quotientLoopProgram
      (38 * (r.length + 1) + 7 * m.length + 32)
      ⟨some 4, readRegs regs 1 3 (some b), quotientStacks (b :: r) m x q⟩
      ⟨some 62, rf, quotientStacks (shiftReduce m r b) m x q⟩ := by
    simpa [relocatePc, stepLabel, shiftReduce, conditionalDifference] using hw
  have hhead := quotientLoop_head regs r m x q b
  have hdigit := quotientLoop_digit rf (shiftReduce m r b) m x q
  have ht := (SubexponentialSAT.Computation.RunsIn.trans
    (⟨3, le_rfl, hhead⟩ : RunsIn quotientLoopProgram 3 _ _) hw').trans
    (⟨3, le_rfl, hdigit⟩ : RunsIn quotientLoopProgram 3 _ _)
  refine ⟨Function.update rf 0 (!(rf 0)), ?_⟩
  convert ht using 1
  · omega
  · simp [quotientBit, hb]

def divideFrom (m q r : List Bool) : List Bool → List Bool × List Bool
  | [] => (q, r)
  | b :: bs => divideFrom m (quotientBit m r b :: q) (shiftReduce m r b) bs

theorem divideFrom_append (m q r xs ys : List Bool) :
    divideFrom m q r (xs ++ ys) =
      let out := divideFrom m q r xs
      divideFrom m out.1 out.2 ys := by
  induction xs generalizing q r with
  | nil => rfl
  | cons b bs ih => exact ih (quotientBit m r b :: q) (shiftReduce m r b)

theorem divideFrom_reverse (m input : List Bool) :
    divideFrom m [] (padTo m []) input.reverse = divide m input := by
  induction input with
  | nil => rfl
  | cons b bs ih =>
    simp [List.reverse_cons, divideFrom_append, divideFrom, divide, ih]

theorem quotientLoop_correct (regs : Fin 8 → Bool) (r m x q : List Bool)
    (hlen : m.length ≤ r.length) :
    ∃ finalRegs,
      RunsIn quotientLoopProgram
        (50 * (x.length + 1) * (r.length + m.length + x.length + 1))
        ⟨some 0, regs, quotientStacks r m x q⟩
        ⟨none, finalRegs,
          quotientStacks (divideFrom m q r x).2 m [] (divideFrom m q r x).1⟩ := by
  induction x generalizing regs r q with
  | nil =>
    refine ⟨readRegs regs 1 3 none, 3, ?_, quotientLoop_exit regs r m q⟩
    simp only [List.length_nil]
    omega
  | cons b bs ih =>
    obtain ⟨r1, h1⟩ := quotientLoop_iteration regs r m bs q b hlen
    have hlen' : m.length ≤ (shiftReduce m r b).length := by rw [shiftReduce_length]; omega
    obtain ⟨rf, h2⟩ := ih r1 (shiftReduce m r b) (quotientBit m r b :: q) hlen'
    refine ⟨rf, ?_⟩
    apply (h1.trans h2).mono
    simp only [List.length_cons, shiftReduce_length]
    nlinarith

abbrev quotientInitializeProgram : Program 8 8 27 :=
  liftProgram initializeProgram id quotientPorts

theorem quotientInitialize_correct (regs : Fin 8 → Bool) (m x : List Bool) :
    ∃ finalRegs,
      Trace quotientInitializeProgram (14 * m.length + 9 * x.length + 18)
        ⟨some 0, regs, quotientStacks [] m x []⟩
        ⟨none, finalRegs, quotientStacks (padTo m []) m x.reverse []⟩ := by
  obtain ⟨rf, hr⟩ := initialize_correct regs m x
  have hw := liftProgram_trace initializeProgram id quotientPorts
    (⟨none, regs, quotientStacks [] [] [] []⟩ : Cfg 8 8 27)
    Function.injective_id quotientPorts_injective hr
  rw [embed_quotient, embed_quotient] at hw
  exact ⟨rf, hw⟩

abbrev quotientProgram : Program 8 8 92 := link quotientInitializeProgram quotientLoopProgram

theorem quotient_correct (regs : Fin 8 → Bool) (m x : List Bool) :
    ∃ finalRegs,
      RunsIn quotientProgram (100 * (m.length + x.length + 1) ^ 2)
        ⟨some 0, regs, quotientStacks [] m x []⟩
        ⟨none, finalRegs, quotientStacks (divide m x).2 m [] (divide m x).1⟩ := by
  obtain ⟨r1, h1⟩ := quotientInitialize_correct regs m x
  obtain ⟨rf, h2⟩ := quotientLoop_correct r1 (padTo m []) m x.reverse [] (by rw [padTo_length])
  have ht := link_runsIn quotientInitializeProgram quotientLoopProgram ⟨_, le_rfl, h1⟩ rfl h2
  have hbound :
      14 * m.length + 9 * x.length + 18 +
        50 * (x.reverse.length + 1) * ((padTo m []).length + m.length + x.reverse.length + 1) ≤
        100 * (m.length + x.length + 1) ^ 2 := by
    simp only [List.length_reverse, padTo_length]
    nlinarith [Nat.zero_le m.length, Nat.zero_le x.length]
  refine ⟨rf, ?_⟩
  simpa [quotientProgram, divideFrom_reverse, relabelCfg, relocatePc] using ht.mono hbound

theorem quotient_value (regs : Fin 8 → Bool) (m x : List Bool)
    (hm : 0 < SubexponentialSAT.BinaryArithmetic.toNat m) :
    ∃ finalRegs quotient remainder,
      RunsIn quotientProgram (100 * (m.length + x.length + 1) ^ 2)
        ⟨some 0, regs, quotientStacks [] m x []⟩
        ⟨none, finalRegs, quotientStacks remainder m [] quotient⟩ ∧
      quotient.length = x.length ∧ remainder.length = m.length + x.length ∧
      SubexponentialSAT.BinaryArithmetic.toNat quotient = SubexponentialSAT.BinaryArithmetic.toNat x / SubexponentialSAT.BinaryArithmetic.toNat m ∧
      SubexponentialSAT.BinaryArithmetic.toNat remainder = SubexponentialSAT.BinaryArithmetic.toNat x % SubexponentialSAT.BinaryArithmetic.toNat m := by
  obtain ⟨rf, hr⟩ := quotient_correct regs m x
  exact ⟨rf, (divide m x).1, (divide m x).2, hr,
    divide_quotient_length m x, divide_remainder_length m x,
    divide_quotient_correct m x hm, divide_remainder_correct m x hm⟩

theorem quotient_primitive (regs : Fin 8 → Bool) (m x : List Bool) :
    ∃ finalRegs,
      SubexponentialSAT.Computation.RunsIn (primitive quotientProgram).step
        (primitiveOverhead quotientProgram * (100 * (m.length + x.length + 1) ^ 2))
        (primitiveCfg quotientProgram ⟨some 0, regs, quotientStacks [] m x []⟩)
        (primitiveCfg quotientProgram
          ⟨none, finalRegs, quotientStacks (divide m x).2 m [] (divide m x).1⟩) := by
  obtain ⟨rf, hr⟩ := quotient_correct regs m x
  exact ⟨rf, primitive_execution _ hr⟩

end SubexponentialSAT.ModularQuotientPrograms

end OAI.Algorithms
