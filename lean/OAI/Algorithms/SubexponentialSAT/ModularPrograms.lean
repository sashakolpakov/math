import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ModularArithmetic
import OAI.Algorithms.SubexponentialSAT.BitProgram
import OAI.Algorithms.SubexponentialSAT.ProgramLinking
import OAI.Algorithms.SubexponentialSAT.StackRoutines
import OAI.Algorithms.SubexponentialSAT.BitProgramCompile

namespace OAI.Algorithms

/-!
# Finite Boolean-stack programs for modular arithmetic

The programs in this file use only a fixed finite collection of labels,
Boolean registers, and Boolean stacks. The operand width and modulus are data.
-/

namespace SubexponentialSAT.ModularPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.ModularArithmetic

/-- A full subtractor using only the Boolean gates in BitProgram.
The two product terms are disjoint, so XOR implements their disjunction. -/
theorem borrowBit_gate_form (a b c : Bool) :
    SubexponentialSAT.ModularArithmetic.borrowBit a b c =
      (((!a) && b) ^^ ((!(a ^^ b)) && c)) := by
  cases a <;> cases b <;> cases c <;> decide

/-- Three operand stacks, eight Boolean registers, and thirteen fixed labels.
Register 0 is the incoming/outgoing borrow. Stacks 0 and 1 are consumed;
stack 2 receives the reversed difference. -/
abbrev subtractProgram : Program 8 3 13 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code label :=
    match label.val with
    | 0 => .pop 0 1 3 1
    | 1 => .branch 3 2 12
    | 2 => .pop 1 2 4 3
    | 3 => .bxor 5 1 2 4
    | 4 => .bxor 6 5 0 5
    | 5 => .bnot 7 1 6
    | 6 => .band 7 7 2 7
    | 7 => .bnot 5 5 8
    | 8 => .band 5 5 0 9
    | 9 => .bxor 0 7 5 10
    | 10 => .push 2 6 11
    | 11 => .goto 0
    | _ => .halt

abbrev operandStacks (left right output : List Bool) (k : Fin 3) : List Bool :=
  if k = 0 then left else if k = 1 then right else output

@[simp] theorem operandStacks_left (left right output : List Bool) :
    operandStacks left right output 0 = left := rfl

@[simp] theorem operandStacks_right (left right output : List Bool) :
    operandStacks left right output 1 = right := rfl

@[simp] theorem operandStacks_output (left right output : List Bool) :
    operandStacks left right output 2 = output := rfl

abbrev subtractCfg (pc : Option (Fin 13)) (regs : Fin 8 → Bool)
    (left right output : List Bool) : Cfg 8 3 13 :=
  ⟨pc, regs, operandStacks left right output⟩

private theorem stacks_update_left (left right output next : List Bool) :
    Function.update (operandStacks left right output) 0 next =
      operandStacks next right output := by
  funext k
  fin_cases k <;> simp [operandStacks]

private theorem stacks_update_right (left right output next : List Bool) :
    Function.update (operandStacks left right output) 1 next =
      operandStacks left next output := by
  funext k
  fin_cases k <;> simp [operandStacks]

private theorem stacks_update_output (left right output next : List Bool) :
    Function.update (operandStacks left right output) 2 next =
      operandStacks left right next := by
  funext k
  fin_cases k <;> simp [operandStacks]

/-- Exact register transformation of one subtraction cell. -/
def roundRegs (regs : Fin 8 → Bool) (a b : Bool) : Fin 8 → Bool :=
  let r := readRegs (readRegs regs 1 3 (some a)) 2 4 (some b)
  let r := Function.update r 5 (a ^^ b)
  let r := Function.update r 6 ((a ^^ b) ^^ regs 0)
  let r := Function.update r 7 (!a)
  let r := Function.update r 7 ((!a) && b)
  let r := Function.update r 5 (!(a ^^ b))
  let r := Function.update r 5 ((!(a ^^ b)) && regs 0)
  Function.update r 0 (((!a) && b) ^^ ((!(a ^^ b)) && regs 0))

theorem roundRegs_borrow (regs : Fin 8 → Bool) (a b : Bool) :
    roundRegs regs a b 0 = borrowBit a b (regs 0) := by
  simp [roundRegs, borrowBit_gate_form]

theorem roundRegs_difference (regs : Fin 8 → Bool) (a b : Bool) :
    roundRegs regs a b 6 = differenceBit a b (regs 0) := by
  simp [roundRegs, differenceBit]

/-- An actual twelve-instruction trace of the fixed Boolean program. -/
theorem subtract_round (regs : Fin 8 → Bool)
    (a b : Bool) (xs ys output : List Bool) :
    Trace subtractProgram 12
      (subtractCfg (some 0) regs (a :: xs) (b :: ys) output)
      (subtractCfg (some 0) (roundRegs regs a b) xs ys
        (differenceBit a b (regs 0) :: output)) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, subtractProgram, execInstr,
    subtractCfg, readRegs, roundRegs, differenceBit,
    stacks_update_left, stacks_update_right, stacks_update_output,
    Function.update_apply]

theorem subtract_exit (regs : Fin 8 → Bool) (output : List Bool) :
    Trace subtractProgram 3
      (subtractCfg (some 0) regs [] [] output)
      (subtractCfg none (readRegs regs 1 3 none) [] [] output) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, subtractProgram, execInstr,
    subtractCfg, readRegs, stacks_update_left,
    Function.update_apply]

/-- Full measured subtraction on arbitrary equal-width operands. -/
theorem subtract_correct (regs : Fin 8 → Bool) (xs ys output : List Bool)
    (hlen : xs.length = ys.length) :
    ∃ finalRegs : Fin 8 → Bool,
      Trace subtractProgram (12 * xs.length + 3)
        (subtractCfg (some 0) regs xs ys output)
        (subtractCfg none finalRegs [] []
          ((subCarry (regs 0) xs ys).1.reverse ++ output)) ∧
      finalRegs 0 = (subCarry (regs 0) xs ys).2 := by
  induction xs generalizing regs ys output with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp hlen.symm
    subst ys
    refine ⟨readRegs regs 1 3 none, ?_, ?_⟩
    · simpa [subCarry] using subtract_exit regs output
    · simp [readRegs, subCarry]
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys =>
      have hl : xs.length = ys.length := by simpa using hlen
      obtain ⟨finalRegs, hrun, hborrow⟩ :=
        ih (roundRegs regs a b) ys (differenceBit a b (regs 0) :: output) hl
      refine ⟨finalRegs, ?_, ?_⟩
      · have h := (subtract_round regs a b xs ys output).trans hrun
        convert h using 1 <;>
          simp [subCarry, roundRegs_borrow, List.reverse_cons, List.append_assoc] ; omega
      · simpa [subCarry, roundRegs_borrow] using hborrow

/-- The final borrow is a comparison result produced by the measured program,
not by a natural-number comparison instruction. -/
theorem subtract_comparison (regs : Fin 8 → Bool) (xs ys : List Bool)
    (hborrow : regs 0 = false) (hlen : xs.length = ys.length) :
    ∃ finalRegs : Fin 8 → Bool,
      Trace subtractProgram (12 * xs.length + 3)
        (subtractCfg (some 0) regs xs ys [])
        (subtractCfg none finalRegs [] [] (subCarry false xs ys).1.reverse) ∧
      (finalRegs 0 = true ↔
        SubexponentialSAT.BinaryArithmetic.toNat xs < SubexponentialSAT.BinaryArithmetic.toNat ys) := by
  obtain ⟨finalRegs, hrun, hfinal⟩ := subtract_correct regs xs ys [] hlen
  refine ⟨finalRegs, ?_, ?_⟩
  · simpa [hborrow] using hrun
  · rw [hfinal, hborrow]
    exact subCarry_borrow_iff xs ys hlen

/-- Pad a modulus word to the width of a shape word. Both input stacks are
consumed; the padded word is pushed in reverse onto output stack 2. -/
abbrev paddingProgram : Program 8 3 5 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code label :=
    match label.val with
    | 0 => .pop 0 1 3 1
    | 1 => .branch 3 2 4
    | 2 => .pop 1 2 4 3
    | 3 => .push 2 2 0
    | _ => .halt

abbrev paddingCfg (pc : Option (Fin 5)) (regs : Fin 8 → Bool)
    (shape input output : List Bool) : Cfg 8 3 5 :=
  ⟨pc, regs, operandStacks shape input output⟩

def paddingRegs (regs : Fin 8 → Bool) (shapeBit : Bool) (input : List Bool) :
    Fin 8 → Bool :=
  readRegs (readRegs regs 1 3 (some shapeBit)) 2 4 input.head?

theorem padding_round (regs : Fin 8 → Bool) (a : Bool)
    (shape input output : List Bool) :
    Trace paddingProgram 4
      (paddingCfg (some 0) regs (a :: shape) input output)
      (paddingCfg (some 0) (paddingRegs regs a input) shape input.tail
        (input.head?.getD false :: output)) := by
  cases input <;>
    apply SubexponentialSAT.Computation.Trace.of_iterate <;>
    simp [Function.iterate_succ_apply, step, paddingProgram, execInstr,
      paddingCfg, paddingRegs, readRegs,
      stacks_update_left, stacks_update_right, stacks_update_output,
      Function.update_apply]

theorem padding_exit (regs : Fin 8 → Bool) (output : List Bool) :
    Trace paddingProgram 3
      (paddingCfg (some 0) regs [] [] output)
      (paddingCfg none (readRegs regs 1 3 none) [] [] output) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, paddingProgram, execInstr,
    paddingCfg, readRegs, stacks_update_left, Function.update_apply]

theorem padding_correct (regs : Fin 8 → Bool) (shape input output : List Bool)
    (hlen : input.length ≤ shape.length) :
    ∃ finalRegs : Fin 8 → Bool,
      Trace paddingProgram (4 * shape.length + 3)
        (paddingCfg (some 0) regs shape input output)
        (paddingCfg none finalRegs [] [] ((padTo shape input).reverse ++ output)) ∧
      finalRegs 0 = regs 0 := by
  induction shape generalizing regs input output with
  | nil =>
    have hi : input = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst input
    refine ⟨readRegs regs 1 3 none, ?_, ?_⟩
    · simpa [padTo] using padding_exit regs output
    · simp [readRegs]
  | cons a shape ih =>
    cases input with
    | nil =>
      obtain ⟨finalRegs, hrun, hreg⟩ :=
        ih (paddingRegs regs a []) [] (false :: output) (Nat.zero_le _)
      refine ⟨finalRegs, ?_, ?_⟩
      · have h := (padding_round regs a shape [] output).trans hrun
        convert h using 1 <;> simp [padTo, List.reverse_cons, List.append_assoc] ; omega
      · simpa [paddingRegs, readRegs] using hreg
    | cons b input =>
      have hl : input.length ≤ shape.length := by simpa using hlen
      obtain ⟨finalRegs, hrun, hreg⟩ :=
        ih (paddingRegs regs a (b :: input)) input (b :: output) hl
      refine ⟨finalRegs, ?_, ?_⟩
      · have h := (padding_round regs a shape (b :: input) output).trans hrun
        convert h using 1 <;> simp [padTo, List.reverse_cons, List.append_assoc] ; omega
      · simpa [paddingRegs, readRegs] using hreg

/-- Reorient the reversed result while preserving the borrow register. -/
abbrev reverseOutput : Program 8 3 4 :=
  SubexponentialSAT.StackRoutines.transferProgram 2 0 1 3

private theorem transfer_output (word : List Bool) :
    SubexponentialSAT.StackRoutines.transferStacks (2 : Fin 3) 0 (operandStacks [] [] word) =
      operandStacks word.reverse [] [] := by
  funext k
  fin_cases k <;> simp [SubexponentialSAT.StackRoutines.transferStacks, operandStacks]

/-- Sequentially link a proved arithmetic run to a proved transfer run.
Both runs execute inside the concrete linked finite instruction table. -/
theorem append_reverse_output {l : ℕ} (p : Program 8 3 l)
    {n : ℕ} {start : Cfg 8 3 l} (regs : Fin 8 → Bool) (word : List Bool)
    (hrun : Trace p n start ⟨none, regs, operandStacks [] [] word⟩) :
    Trace (SubexponentialSAT.ProgramLinking.link p reverseOutput)
      (n + 3 * word.length + 3)
      (SubexponentialSAT.ProgramLinking.relabelCfg (Fin.castAdd 4)
        (some (Fin.natAdd l reverseOutput.entry)) start)
      ⟨none, readRegs regs 1 3 none, operandStacks word.reverse [] []⟩ := by
  have ht := SubexponentialSAT.StackRoutines.transferProgram_trace
    (2 : Fin 3) 0 (1 : Fin 8) 3 (by decide) (by decide)
    regs (operandStacks [] [] word)
  have hh := SubexponentialSAT.StackRoutines.halt_after_trace reverseOutput ht
    (3 : Fin 4) rfl rfl
  have hlink := SubexponentialSAT.ProgramLinking.link_trace p reverseOutput hrun rfl hh
  simpa [SubexponentialSAT.ProgramLinking.relabelCfg, SubexponentialSAT.ProgramLinking.relocatePc,
    SubexponentialSAT.StackRoutines.transferResult, transfer_output, Nat.add_assoc] using hlink

abbrev subtractLEProgram : Program 8 3 17 :=
  SubexponentialSAT.ProgramLinking.link subtractProgram reverseOutput

/-- A reusable subtraction program returning a little-endian result.
Its exact cost includes the result-reversal routine and both return jumps. -/
theorem subtractLE_correct (regs : Fin 8 → Bool) (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    ∃ finalRegs : Fin 8 → Bool,
      Trace subtractLEProgram (15 * xs.length + 6)
        ⟨some 0, regs, operandStacks xs ys []⟩
        ⟨none, finalRegs, operandStacks (subCarry (regs 0) xs ys).1 [] []⟩ ∧
      finalRegs 0 = (subCarry (regs 0) xs ys).2 := by
  obtain ⟨midRegs, hrun, hborrow⟩ := subtract_correct regs xs ys [] hlen
  have hrun' : Trace subtractProgram (12 * xs.length + 3)
      (subtractCfg (some 0) regs xs ys [])
      ⟨none, midRegs, operandStacks [] [] (subCarry (regs 0) xs ys).1.reverse⟩ := by
    simpa [subtractCfg] using hrun
  have hout := append_reverse_output subtractProgram midRegs _ hrun'
  refine ⟨readRegs midRegs 1 3 none, ?_, ?_⟩
  · convert hout using 1
    · rw [List.length_reverse, subCarry_length _ _ _ hlen]
      omega
    · rfl
    · rw [List.reverse_reverse]
  · simpa [readRegs] using hborrow

abbrev paddingLEProgram : Program 8 3 9 :=
  SubexponentialSAT.ProgramLinking.link paddingProgram reverseOutput

theorem paddingLE_correct (regs : Fin 8 → Bool) (shape input : List Bool)
    (hlen : input.length ≤ shape.length) :
    ∃ finalRegs : Fin 8 → Bool,
      Trace paddingLEProgram (7 * shape.length + 6)
        ⟨some 0, regs, operandStacks shape input []⟩
        ⟨none, finalRegs, operandStacks (padTo shape input) [] []⟩ ∧
      finalRegs 0 = regs 0 := by
  obtain ⟨midRegs, hrun, hborrow⟩ := padding_correct regs shape input [] hlen
  have hrun' : Trace paddingProgram (4 * shape.length + 3)
      (paddingCfg (some 0) regs shape input [])
      ⟨none, midRegs, operandStacks [] [] (padTo shape input).reverse⟩ := by
    simpa [paddingCfg] using hrun
  have hout := append_reverse_output paddingProgram midRegs _ hrun'
  refine ⟨readRegs midRegs 1 3 none, ?_, ?_⟩
  · convert hout using 1
    · rw [List.length_reverse, padTo_length]
      omega
    · rfl
    · rw [List.reverse_reverse]
  · simpa [readRegs] using hborrow

/-! Preserve a candidate word while subtracting a modulus from its copy. -/

def subtractionPorts : Fin 3 → Fin 5 := ![2, 1, 3]

theorem subtractionPorts_injective : Function.Injective subtractionPorts := by decide

abbrev wideStacks (saved left right output : List Bool) (k : Fin 5) : List Bool :=
  if k = 0 then saved else if k = 1 then right else if k = 2 then left
  else if k = 3 then output else []

abbrev subtractWideProgram : Program 8 5 13 where
  inputStack := 2
  outputStack := 3
  entry := 0
  code pc := SubexponentialSAT.ProgramLinking.relocateInstr id subtractionPorts id none
    (subtractProgram.code pc)

private theorem embed_subtract (pc : Option (Fin 13)) (regs : Fin 8 → Bool)
    (saved left right output : List Bool) :
    SubexponentialSAT.ProgramLinking.embedCfg id subtractionPorts id none
      (⟨none, regs, wideStacks saved [] [] []⟩ : Cfg 8 5 13)
      (subtractCfg pc regs left right output) =
      (⟨pc, regs, wideStacks saved left right output⟩ : Cfg 8 5 13) := by
  classical
  suffices hpc :
      (SubexponentialSAT.ProgramLinking.embedCfg id subtractionPorts id none
        (⟨none, regs, wideStacks saved [] [] []⟩ : Cfg 8 5 13)
        (subtractCfg pc regs left right output)).pc = pc by
    suffices hregs :
        (SubexponentialSAT.ProgramLinking.embedCfg id subtractionPorts id none
          (⟨none, regs, wideStacks saved [] [] []⟩ : Cfg 8 5 13)
          (subtractCfg pc regs left right output)).regs = regs by
      suffices hstk :
          (SubexponentialSAT.ProgramLinking.embedCfg id subtractionPorts id none
            (⟨none, regs, wideStacks saved [] [] []⟩ : Cfg 8 5 13)
            (subtractCfg pc regs left right output)).stacks =
              wideStacks saved left right output by
        cases he : SubexponentialSAT.ProgramLinking.embedCfg id subtractionPorts id none
            (⟨none, regs, wideStacks saved [] [] []⟩ : Cfg 8 5 13)
            (subtractCfg pc regs left right output)
        simp_all
      funext k
      fin_cases k
      · exact SubexponentialSAT.ProgramLinking.embedCfg_stack_frame id subtractionPorts id none
          _ _ 0 (by decide)
      · simpa [subtractionPorts, subtractCfg, wideStacks, operandStacks] using
          SubexponentialSAT.ProgramLinking.embedCfg_stack id subtractionPorts id none
            (⟨none, regs, wideStacks saved [] [] []⟩ : Cfg 8 5 13)
            (subtractCfg pc regs left right output) subtractionPorts_injective (1 : Fin 3)
      · simpa [subtractionPorts, subtractCfg, wideStacks, operandStacks] using
          SubexponentialSAT.ProgramLinking.embedCfg_stack id subtractionPorts id none
            (⟨none, regs, wideStacks saved [] [] []⟩ : Cfg 8 5 13)
            (subtractCfg pc regs left right output) subtractionPorts_injective (0 : Fin 3)
      · simpa [subtractionPorts, subtractCfg, wideStacks, operandStacks] using
          SubexponentialSAT.ProgramLinking.embedCfg_stack id subtractionPorts id none
            (⟨none, regs, wideStacks saved [] [] []⟩ : Cfg 8 5 13)
            (subtractCfg pc regs left right output) subtractionPorts_injective (2 : Fin 3)
      · exact SubexponentialSAT.ProgramLinking.embedCfg_stack_frame id subtractionPorts id none
          _ _ 4 (by decide)
    simp [SubexponentialSAT.ProgramLinking.embedCfg ]
  cases pc <;> rfl

theorem subtractWide_correct (regs : Fin 8 → Bool)
    (saved xs ys : List Bool) (hlen : xs.length = ys.length) :
    ∃ finalRegs : Fin 8 → Bool,
      Trace subtractWideProgram (12 * xs.length + 3)
        ⟨some 0, regs, wideStacks saved xs ys []⟩
        ⟨none, finalRegs, wideStacks saved [] [] (subCarry (regs 0) xs ys).1.reverse⟩ ∧
      finalRegs 0 = (subCarry (regs 0) xs ys).2 := by
  obtain ⟨finalRegs, hrun, hborrow⟩ := subtract_correct regs xs ys [] hlen
  have hw := SubexponentialSAT.ProgramLinking.relocate_trace subtractProgram subtractWideProgram
    id subtractionPorts id none
    (⟨none, regs, wideStacks saved [] [] []⟩ : Cfg 8 5 13)
    Function.injective_id subtractionPorts_injective (fun _ => rfl) hrun
  refine ⟨finalRegs, ?_, hborrow⟩
  have hstart := embed_subtract (some 0) regs saved xs ys []
  rw [hstart] at hw
  have hend :
      SubexponentialSAT.ProgramLinking.embedCfg id subtractionPorts id none
        (⟨none, regs, wideStacks saved [] [] []⟩ : Cfg 8 5 13)
        (subtractCfg none finalRegs [] [] ((subCarry (regs 0) xs ys).1.reverse ++ [])) =
        (⟨none, finalRegs, wideStacks saved [] [] (subCarry (regs 0) xs ys).1.reverse⟩ :
          Cfg 8 5 13) := by
    have h := embed_subtract none finalRegs saved [] []
      (subCarry (regs 0) xs ys).1.reverse
    simpa [SubexponentialSAT.ProgramLinking.embedCfg, subtractCfg] using h
  rwa [hend] at hw

abbrev copyCandidateProgram : Program 8 5 8 :=
  SubexponentialSAT.StackRoutines.copyProgram 0 2 4 1 3

private theorem copy_candidate (candidate modulus : List Bool) :
    SubexponentialSAT.StackRoutines.copyStacks (0 : Fin 5) 2
      (wideStacks candidate [] modulus []) =
      wideStacks candidate candidate modulus [] := by
  funext k
  fin_cases k <;> simp [SubexponentialSAT.StackRoutines.copyStacks, wideStacks]

abbrev copyAndSubtractProgram : Program 8 5 21 :=
  SubexponentialSAT.ProgramLinking.link copyCandidateProgram subtractWideProgram

theorem copyAndSubtract_correct (regs : Fin 8 → Bool)
    (candidate modulus : List Bool) (hlen : candidate.length = modulus.length) :
    ∃ finalRegs : Fin 8 → Bool,
      Trace copyAndSubtractProgram (19 * candidate.length + 8)
        ⟨some 0, regs, wideStacks candidate [] modulus []⟩
        ⟨none, finalRegs, wideStacks candidate [] []
          (subCarry (regs 0) candidate modulus).1.reverse⟩ ∧
      finalRegs 0 = (subCarry (regs 0) candidate modulus).2 := by
  have hc := SubexponentialSAT.StackRoutines.copyProgram_trace
    (0 : Fin 5) 2 4 (1 : Fin 8) 3 (by decide) (by decide) (by decide)
    (by decide) regs (wideStacks candidate [] modulus []) (by simp [wideStacks])
  have hh := SubexponentialSAT.StackRoutines.halt_after_trace copyCandidateProgram hc
    (7 : Fin 8) rfl rfl
  have hh' : Trace copyCandidateProgram (7 * candidate.length + 5)
      ⟨some 0, regs, wideStacks candidate [] modulus []⟩
      ⟨none, readRegs regs 1 3 none, wideStacks candidate candidate modulus []⟩ := by
    simpa [SubexponentialSAT.StackRoutines.copyResult, copy_candidate, wideStacks, Nat.add_assoc]
      using hh
  obtain ⟨finalRegs, hs, hb⟩ := subtractWide_correct
    (readRegs regs 1 3 none) candidate candidate modulus hlen
  have hs' : Trace subtractWideProgram (12 * candidate.length + 3)
      (SubexponentialSAT.ProgramLinking.enter subtractWideProgram
        (⟨none, readRegs regs 1 3 none,
          wideStacks candidate candidate modulus []⟩ : Cfg 8 5 8))
      ⟨none, finalRegs, wideStacks candidate [] []
        (subCarry (regs 0) candidate modulus).1.reverse⟩ := by
    simpa [SubexponentialSAT.ProgramLinking.enter, subtractWideProgram, readRegs] using hs
  have ht := SubexponentialSAT.ProgramLinking.link_trace copyCandidateProgram
    subtractWideProgram hh' rfl hs'
  refine ⟨finalRegs, ?_, ?_⟩
  · convert ht using 1
    · omega
    · rfl
    · rfl
  · simpa [readRegs] using hb

/-- Select the saved candidate on borrow; otherwise reverse the difference.
The unused candidate and all work stacks are consumed in either branch. -/
abbrev selectDifferenceProgram : Program 8 5 10 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code := ![.branch 0 1 3,
    .pop 3 1 3 2, .branch 3 1 9,
    .pop 0 1 3 4, .branch 3 3 5,
    .pop 3 1 3 6, .branch 3 7 9, .push 0 1 5,
    .halt, .halt]

private theorem clear_difference (candidate difference : List Bool) :
    SubexponentialSAT.StackRoutines.clearStacks (3 : Fin 5)
      (wideStacks candidate [] [] difference) =
      wideStacks candidate [] [] [] := by
  funext k
  fin_cases k <;> simp [SubexponentialSAT.StackRoutines.clearStacks, wideStacks]

private theorem clear_candidate (candidate difference : List Bool) :
    SubexponentialSAT.StackRoutines.clearStacks (0 : Fin 5)
      (wideStacks candidate [] [] difference) =
      wideStacks [] [] [] difference := by
  funext k
  fin_cases k <;> simp [SubexponentialSAT.StackRoutines.clearStacks, wideStacks]

private theorem transfer_difference (difference : List Bool) :
    SubexponentialSAT.StackRoutines.transferStacks (3 : Fin 5) 0
      (wideStacks [] [] [] difference) =
      wideStacks difference.reverse [] [] [] := by
  funext k
  fin_cases k <;> simp [SubexponentialSAT.StackRoutines.transferStacks, wideStacks]

theorem selectDifference_borrow (regs : Fin 8 → Bool)
    (candidate difference : List Bool) (hborrow : regs 0 = true) :
    Trace selectDifferenceProgram (2 * difference.length + 4)
      ⟨some 0, regs, wideStacks candidate [] [] difference⟩
      ⟨none, readRegs regs 1 3 none, wideStacks candidate [] [] []⟩ := by
  have hc := SubexponentialSAT.StackRoutines.clear_trace selectDifferenceProgram
    (3 : Fin 5) (1 : Fin 8) 3 1 2 9 rfl rfl
    regs (wideStacks candidate [] [] difference)
  have hh := SubexponentialSAT.StackRoutines.halt_after_trace selectDifferenceProgram hc
    (9 : Fin 10) rfl rfl
  have ht := SubexponentialSAT.Computation.Trace.cons
    (a := (⟨some 0, regs, wideStacks candidate [] [] difference⟩ : Cfg 8 5 10))
    (by simp [step, execInstr, hborrow]) hh
  simpa [SubexponentialSAT.StackRoutines.clearResult, clear_difference, wideStacks, Nat.add_assoc]
    using ht

theorem selectDifference_noBorrow (regs : Fin 8 → Bool)
    (candidate difference : List Bool) (hborrow : regs 0 = false) :
    Trace selectDifferenceProgram (2 * candidate.length + 3 * difference.length + 6)
      ⟨some 0, regs, wideStacks candidate [] [] difference⟩
      ⟨none, readRegs regs 1 3 none, wideStacks difference.reverse [] [] []⟩ := by
  have hc := SubexponentialSAT.StackRoutines.clear_trace selectDifferenceProgram
    (0 : Fin 5) (1 : Fin 8) 3 3 4 5 rfl rfl
    regs (wideStacks candidate [] [] difference)
  have hc' : Trace selectDifferenceProgram (2 * candidate.length + 2)
      ⟨some 3, regs, wideStacks candidate [] [] difference⟩
      ⟨some 5, readRegs regs 1 3 none, wideStacks [] [] [] difference⟩ := by
    simpa [SubexponentialSAT.StackRoutines.clearResult, clear_candidate, wideStacks] using hc
  have hm := SubexponentialSAT.StackRoutines.transfer_trace selectDifferenceProgram
    (3 : Fin 5) 0 (1 : Fin 8) 3 5 6 7 9 (by decide) (by decide)
    rfl rfl rfl (readRegs regs 1 3 none) (wideStacks [] [] [] difference)
  have hh := SubexponentialSAT.StackRoutines.halt_after_trace selectDifferenceProgram hm
    (9 : Fin 10) rfl rfl
  have hh' : Trace selectDifferenceProgram (3 * difference.length + 3)
      ⟨some 5, readRegs regs 1 3 none, wideStacks [] [] [] difference⟩
      ⟨none, readRegs regs 1 3 none, wideStacks difference.reverse [] [] []⟩ := by
    simpa [SubexponentialSAT.StackRoutines.transferResult, transfer_difference, wideStacks,
      SubexponentialSAT.StackRoutines.readRegs_reset, Nat.add_assoc] using hh
  have ht := SubexponentialSAT.Computation.Trace.cons
    (a := (⟨some 0, regs, wideStacks candidate [] [] difference⟩ : Cfg 8 5 10))
    (by simp [step, execInstr, hborrow]) (hc'.trans hh')
  convert ht using 1
  omega

abbrev conditionalSubtractProgram : Program 8 5 31 :=
  SubexponentialSAT.ProgramLinking.link copyAndSubtractProgram selectDifferenceProgram

def conditionalDifference (candidate modulus : List Bool) : List Bool :=
  let d := subCarry false candidate modulus
  if d.2 then candidate else d.1

theorem conditionalSubtract_correct (regs : Fin 8 → Bool) (hzero : regs 0 = false)
    (candidate modulus : List Bool) (hlen : candidate.length = modulus.length) :
    ∃ finalRegs : Fin 8 → Bool,
      RunsIn conditionalSubtractProgram (24 * candidate.length + 14)
        ⟨some 0, regs, wideStacks candidate [] modulus []⟩
        ⟨none, finalRegs,
          wideStacks (conditionalDifference candidate modulus) [] [] []⟩ ∧
      finalRegs 0 = (subCarry false candidate modulus).2 := by
  obtain ⟨midRegs, hp, hb⟩ := copyAndSubtract_correct regs candidate modulus hlen
  rw [hzero] at hp hb
  refine ⟨readRegs midRegs 1 3 none, ?_, ?_⟩
  · cases hd : (subCarry false candidate modulus).2
    · have hs := selectDifference_noBorrow midRegs candidate
        (subCarry false candidate modulus).1.reverse (hb.trans hd)
      have ht := SubexponentialSAT.ProgramLinking.link_trace copyAndSubtractProgram
        selectDifferenceProgram hp rfl hs
      refine ⟨19 * candidate.length + 8 +
        (2 * candidate.length + 3 * (subCarry false candidate modulus).1.reverse.length + 6),
        ?_, ?_⟩
      · simp only [List.length_reverse, subCarry_length _ _ _ hlen]
        omega
      · simpa [conditionalSubtractProgram, conditionalDifference, hd,
          SubexponentialSAT.ProgramLinking.relabelCfg, SubexponentialSAT.ProgramLinking.relocatePc]
          using ht
    · have hs := selectDifference_borrow midRegs candidate
        (subCarry false candidate modulus).1.reverse (hb.trans hd)
      have ht := SubexponentialSAT.ProgramLinking.link_trace copyAndSubtractProgram
        selectDifferenceProgram hp rfl hs
      refine ⟨19 * candidate.length + 8 +
        (2 * (subCarry false candidate modulus).1.reverse.length + 4), ?_, ?_⟩
      · simp only [List.length_reverse, subCarry_length _ _ _ hlen]
        omega
      · simpa [conditionalSubtractProgram, conditionalDifference, hd,
          SubexponentialSAT.ProgramLinking.relabelCfg, SubexponentialSAT.ProgramLinking.relocatePc]
          using ht
  · simpa [readRegs] using hb

theorem conditionalDifference_length (candidate modulus : List Bool)
    (hlen : candidate.length = modulus.length) :
    (conditionalDifference candidate modulus).length = candidate.length := by
  dsimp only [conditionalDifference]
  split
  · rfl
  · exact subCarry_length false candidate modulus hlen

theorem conditionalDifference_value (candidate modulus : List Bool)
    (hlen : candidate.length = modulus.length)
    (_hmod : 0 < SubexponentialSAT.BinaryArithmetic.toNat modulus)
    (hsmall : SubexponentialSAT.BinaryArithmetic.toNat candidate < 2 * SubexponentialSAT.BinaryArithmetic.toNat modulus) :
    SubexponentialSAT.BinaryArithmetic.toNat (conditionalDifference candidate modulus) =
      SubexponentialSAT.BinaryArithmetic.toNat candidate % SubexponentialSAT.BinaryArithmetic.toNat modulus := by
  have hb := subCarry_borrow_iff candidate modulus hlen
  have hv := subCarry_correct false candidate modulus hlen
  cases hd : (subCarry false candidate modulus).2
  · have hle : SubexponentialSAT.BinaryArithmetic.toNat modulus ≤
        SubexponentialSAT.BinaryArithmetic.toNat candidate := by
      rw [hd] at hb
      simp only [Bool.false_eq_true, false_iff, not_lt] at hb
      exact hb
    simp only [hd, SubexponentialSAT.BinaryArithmetic.bitVal_false, Nat.mul_zero, Nat.add_zero] at hv
    have hsub : SubexponentialSAT.BinaryArithmetic.toNat (subCarry false candidate modulus).1 =
        SubexponentialSAT.BinaryArithmetic.toNat candidate - SubexponentialSAT.BinaryArithmetic.toNat modulus := by omega
    simp only [conditionalDifference, hd, Bool.false_eq_true, ↓reduceIte, hsub]
    rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt]
    omega
  · have hlt := hb.mp hd
    simp [conditionalDifference, hd, Nat.mod_eq_of_lt hlt]

theorem conditionalSubtract_primitive (regs : Fin 8 → Bool) (hzero : regs 0 = false)
    (candidate modulus : List Bool) (hlen : candidate.length = modulus.length) :
    ∃ finalRegs : Fin 8 → Bool,
      SubexponentialSAT.Computation.RunsIn (primitive conditionalSubtractProgram).step
        (primitiveOverhead conditionalSubtractProgram * (24 * candidate.length + 14))
        (primitiveCfg conditionalSubtractProgram
          ⟨some 0, regs, wideStacks candidate [] modulus []⟩)
        (primitiveCfg conditionalSubtractProgram
          ⟨none, finalRegs,
            wideStacks (conditionalDifference candidate modulus) [] [] []⟩) ∧
      finalRegs 0 = (subCarry false candidate modulus).2 := by
  obtain ⟨finalRegs, hrun, hborrow⟩ :=
    conditionalSubtract_correct regs hzero candidate modulus hlen
  exact ⟨finalRegs, primitive_execution _ hrun, hborrow⟩

end SubexponentialSAT.ModularPrograms

end OAI.Algorithms
