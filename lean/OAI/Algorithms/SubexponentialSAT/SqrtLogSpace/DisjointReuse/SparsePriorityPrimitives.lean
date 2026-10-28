import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryCompareProgram
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.StackRoutines
import OAI.Algorithms.SubexponentialSAT.FrontendProgram
import OAI.Algorithms.SubexponentialSAT.SubexpSunflowerProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import Mathlib.Tactic.Linarith

/-! Concrete record-count and emission primitives extracted from supplied sources.
No sparsification schedule or formula evaluator is imported. Provenance is recorded
in verification/counting-draft/worker04/extraction.json. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives

open BitProgram StructuredCalls BinaryArithmetic

namespace Tuple
abbrev Data := State 13 9

def moved (src dst : Fin 9) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩

def move (src dst : Fin 9) : Cmd 13 9 :=
  .call (StackRoutines.transferProgram src dst 0 1)

theorem move_eval (src dst : Fin 9) (h : src ≠ dst) (d : Data) :
    Eval (move src dst) (3 * (d.stacks src).length + 3) d (moved src dst d) := by
  have ht := StackRoutines.transferProgram_trace src dst (0 : Fin 13) 1 h (by decide)
    d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ ht 3 rfl rfl
  apply Eval.call
  simpa [moved, StackRoutines.transferResult, StackRoutines.transferProgram,
    StructuredProgram.State.withPC, Nat.add_assoc] using hh

def copied (src dst : Fin 9) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

def copy (src dst : Fin 9) : Cmd 13 9 :=
  .call (StackRoutines.copyProgram src dst 8 0 1)

theorem copy_eval (src dst : Fin 9) (d : Data)
    (hsd : src ≠ dst) (hst : src ≠ 8) (htd : (8 : Fin 9) ≠ dst)
    (htmp : d.stacks 8 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (copied src dst d) := by
  have ht := StackRoutines.copyProgram_trace src dst 8 (0 : Fin 13) 1
    hsd hst htd (by decide) d.regs d.stacks htmp
  have hh := StackRoutines.halt_after_trace _ ht 7 rfl rfl
  apply Eval.call
  simpa [copied, StackRoutines.copyResult, StackRoutines.copyProgram,
    StructuredProgram.State.withPC, Nat.add_assoc] using hh

def cleared (port : Fin 9) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks port d.stacks⟩

def clear (port : Fin 9) : Cmd 13 9 := .call (StackRoutines.clearProgram port 0 1)

theorem clear_eval (port : Fin 9) (d : Data) :
    Eval (clear port) (2 * (d.stacks port).length + 3) d (cleared port d) := by
  have ht := StackRoutines.clearProgram_trace port (0 : Fin 13) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ ht 2 rfl rfl
  apply Eval.call
  simpa [cleared, StackRoutines.clearResult, StackRoutines.clearProgram,
    StructuredProgram.State.withPC, Nat.add_assoc] using hh

def workReg (i : Fin 8) : Fin 13 := Fin.castAdd 5 i
def pairPort (left right : Fin 9) (i : Fin 2) : Fin 9 := if i = 0 then left else right

theorem workReg_injective : Function.Injective workReg := Fin.castAdd_injective 8 5

theorem pairPort_injective (left right : Fin 9) (h : left ≠ right) :
    Function.Injective (pairPort left right) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [pairPort]

def compare (left right : Fin 9) : Cmd 13 9 :=
  .call (ProgramLinking.liftProgram BinaryCompareProgram.Compare.program workReg (pairPort left right))

theorem compare_eval (left right : Fin 9) (h : left ≠ right) (d : Data) :
    ∃ e : Data,
      Eval (compare left right)
        (10 * max (d.stacks left).length (d.stacks right).length + 6) d e ∧
      e.regs 0 = decide (toNat (d.stacks left) < toNat (d.stacks right)) ∧
      (∀ i : Fin 13, 8 ≤ i.val → e.regs i = d.regs i) ∧
      (∀ i : Fin 9, i ≠ left → i ≠ right → e.stacks i = d.stacks i) ∧
      e.stacks left = [] ∧ e.stacks right = [] := by
  obtain ⟨e, he, ha, hr, hs, hz⟩ := BinaryCompareProgram.compare_call workReg
    (pairPort left right) workReg_injective (pairPort_injective left right h) d
  refine ⟨e, he, ?_, ?_, ?_, hz 0, hz 1⟩
  · apply Bool.eq_iff_iff.mpr
    simpa [workReg, pairPort] using ha
  · intro i hi
    apply hr
    rintro ⟨j, hj⟩
    have hjv := congrArg Fin.val hj
    change j.val = i.val at hjv
    have := j.isLt
    omega
  · intro i hl hr'
    apply hs
    rintro ⟨j, hj⟩
    fin_cases j <;> simp [pairPort] at hj <;> subst i <;> contradiction

end Tuple

namespace Count

open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives.Tuple
  (Data copied copy copy_eval moved move move_eval cleared clear clear_eval)

def countReg (i : Fin 2) : Fin 13 := Fin.castAdd 11 i
def countStack (i : Fin 2) : Fin 9 := if i = 0 then 5 else 7

theorem countReg_injective : Function.Injective countReg := Fin.castAdd_injective 2 11
theorem countStack_injective : Function.Injective countStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [countStack]

def countProgram := ProgramLinking.liftProgram SubexpSunflowerProgram.CountRecords.program
  countReg countStack

def counted (records : List (List Bool)) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks 5 []) 7 (Encoding.encodeNat records.length)⟩

theorem count_eval (records : List (List Bool)) (d : Data)
    (hinput : d.stacks 5 = Encoding.encodeList id records) (houtput : d.stacks 7 = []) :
    Eval (.call countProgram) (SubexpSunflowerProgram.CountRecords.steps records)
      d (counted records d) := by
  let b : State 2 2 := ⟨ParserProgram.pair false false,
    ParserProgram.pair [] (Encoding.encodeNat records.length)⟩
  have hstart : (projectState countReg countStack d).withPC
      (some SubexpSunflowerProgram.CountRecords.program.entry) =
      SubexpSunflowerProgram.CountRecords.cfg
        (some SubexpSunflowerProgram.CountRecords.program.entry) (d.regs 0) (d.regs 1)
        (Encoding.encodeList id records) [] := by
    simp only [projectState, StructuredProgram.State.withPC,
      SubexpSunflowerProgram.CountRecords.cfg, Cfg.mk.injEq, true_and]
    constructor <;> funext i <;> fin_cases i <;>
      simp [countReg, countStack, ParserProgram.pair, hinput, houtput]
  have ht : Trace SubexpSunflowerProgram.CountRecords.program
      (SubexpSunflowerProgram.CountRecords.steps records)
      ((projectState countReg countStack d).withPC
        (some SubexpSunflowerProgram.CountRecords.program.entry)) (b.withPC none) := by
    rw [hstart]
    simpa [b, SubexpSunflowerProgram.CountRecords.cfg, StructuredProgram.State.withPC] using
      SubexpSunflowerProgram.CountRecords.trace records [] [] (d.regs 0) (d.regs 1)
  have hb : embedState countReg countStack d b = counted records d := by
    apply embedState_eq_of_ports _ _ _ _ _ countReg_injective countStack_injective
    · intro i; fin_cases i <;> simp [counted, countReg, readRegs, b]
    · intro i hi
      have hi0 : i ≠ 0 := by intro h; apply hi; exact ⟨0, h.symm⟩
      have hi1 : i ≠ 1 := by intro h; apply hi; exact ⟨1, h.symm⟩
      simp [counted, readRegs, hi0, hi1]
    · intro i; fin_cases i <;> simp [counted, countStack, b]
    · intro i hi
      have hi5 : i ≠ 5 := by intro h; apply hi; exact ⟨0, h.symm⟩
      have hi7 : i ≠ 7 := by intro h; apply hi; exact ⟨1, h.symm⟩
      simp [counted, hi5, hi7]
  simpa only [hb, countProgram] using eval_call_from_state
    SubexpSunflowerProgram.CountRecords.program countReg countStack d
    countReg_injective countStack_injective ht

def reset : Cmd 13 9 :=
  .seq (RecordPrograms.atom (.set 0 false))
    (.seq (RecordPrograms.atom (.set 1 false)) (RecordPrograms.atom (.set 2 false)))

def resetState (d : Data) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 false) 2 false, d.stacks⟩

theorem reset_eval (d : Data) : Eval reset 3 d (resetState d) :=
  .seq (.base (.atom _ _)) (.seq (.base (.atom _ _)) (.base (.atom _ _)))

def binaryReg (i : Fin 3) : Fin 13 := Fin.castAdd 10 i
def binaryStack (i : Fin 4) : Fin 9 :=
  if i = 0 then 7 else if i = 1 then 5 else if i = 2 then 6 else 8

theorem binaryReg_injective : Function.Injective binaryReg := Fin.castAdd_injective 3 10
theorem binaryStack_injective : Function.Injective binaryStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [binaryStack]

def binaryProgram := ProgramLinking.liftProgram FrontendProgram.initializeProgram binaryReg binaryStack
def toBinary : Cmd 13 9 := .seq reset (.call binaryProgram)

/-- Convert an input-sized unary record count to binary. The cost comes from
the actual header parser and dynamic binary length counter. -/
theorem toBinary_eval (n : ℕ) (d : Data) (h7 : d.stacks 7 = Encoding.encodeNat n)
    (h5 : d.stacks 5 = []) (h6 : d.stacks 6 = []) (h8 : d.stacks 8 = []) :
    ∃ t ≤ FrontendProgram.initializeBound n + 3, ∃ bits : List Bool, ∃ e : Data,
      Eval toBinary t d e ∧ toNat bits = n ∧ bits.length ≤ n ∧
      e.stacks = Function.update (Function.update d.stacks 7 []) 6 bits ∧
      (∀ i : Fin 13, 3 ≤ i.val → e.regs i = d.regs i) := by
  obtain ⟨bits, hvalue, hlength, t, ht, htrace⟩ := FrontendProgram.initialize_raw n []
  let a := resetState d
  let b : State 3 4 := StructuredProgram.State.ofCfg
    (FrontendProgram.cfg none false false [] [] bits [])
  have hstart : (projectState binaryReg binaryStack a).withPC
      (some FrontendProgram.initializeProgram.entry) =
      initial FrontendProgram.initializeProgram (Encoding.encodeNat n ++ []) := by
    rw [FrontendProgram.initialize_initial]
    simp only [projectState, StructuredProgram.State.withPC, FrontendProgram.cfg,
      Cfg.mk.injEq]
    refine ⟨rfl, ?_, ?_⟩
    · funext i
      fin_cases i <;> simp [a, resetState, binaryReg, CounterPrograms.counterRegs]
    · funext i
      fin_cases i <;> simp [a, resetState, binaryStack, FrontendProgram.storage,
        h7, h5, h6, h8]
  have hl : Trace FrontendProgram.initializeProgram t
      ((projectState binaryReg binaryStack a).withPC
        (some FrontendProgram.initializeProgram.entry)) (b.withPC none) := by
    rw [hstart]
    exact htrace
  have he := eval_call_from_state FrontendProgram.initializeProgram binaryReg binaryStack a
    binaryReg_injective binaryStack_injective hl
  let e := embedState binaryReg binaryStack a b
  have hs (i : Fin 4) : e.stacks (binaryStack i) = b.stacks i :=
    embedState_stack _ _ _ _ binaryStack_injective i
  refine ⟨3 + t, by omega, bits, e, Eval.seq (reset_eval d) he, ?_, hlength, ?_, ?_⟩
  · simpa only [CounterPrograms.value_eq_toNat] using hvalue
  · funext i
    fin_cases i
    · exact embedState_stack_frame _ _ _ _ _ (by decide)
    · exact embedState_stack_frame _ _ _ _ _ (by decide)
    · exact embedState_stack_frame _ _ _ _ _ (by decide)
    · exact embedState_stack_frame _ _ _ _ _ (by decide)
    · exact embedState_stack_frame _ _ _ _ _ (by decide)
    · simpa [binaryStack, b, FrontendProgram.cfg, FrontendProgram.storage,
        StructuredProgram.State.ofCfg, h5] using hs 1
    · simpa [binaryStack, b, FrontendProgram.cfg, FrontendProgram.storage,
        StructuredProgram.State.ofCfg] using hs 2
    · simpa [binaryStack, b, FrontendProgram.cfg, FrontendProgram.storage,
        StructuredProgram.State.ofCfg] using hs 0
    · simpa [binaryStack, b, FrontendProgram.cfg, FrontendProgram.storage,
        StructuredProgram.State.ofCfg, h8] using hs 3
  · intro i hi
    have hfr : e.regs i = a.regs i := by
      apply embedState_register_frame
      rintro ⟨j, hj⟩
      have hjv := congrArg Fin.val hj
      change j.val = i.val at hjv
      have := j.isLt
      omega
    have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
    have hi1 : i ≠ 1 := by intro h; subst i; simp at hi
    have hi2 : i ≠ 2 := by intro h; subst i; simp at hi
    simpa [a, resetState, hi0, hi1, hi2] using hfr

def expectedPort (i : Fin 2) : Fin 9 := if i = 0 then 3 else 4

def less (left right : Fin 9) : Cmd 13 9 :=
  .seq (copy left 5) (.seq (copy right 7) (Tuple.compare 5 7))

theorem less_eval (left right : Fin 9) (d : Data)
    (hl : left ≠ 5 ∧ left ≠ 7 ∧ left ≠ 8)
    (hr : right ≠ 5 ∧ right ≠ 7 ∧ right ≠ 8)
    (h5 : d.stacks 5 = []) (h7 : d.stacks 7 = []) (h8 : d.stacks 8 = []) :
    ∃ n ≤ 20 * ((d.stacks left).length + (d.stacks right).length + 1), ∃ e : Data,
      Eval (less left right) n d e ∧ e.stacks = d.stacks ∧
      e.regs 0 = decide (toNat (d.stacks left) < toNat (d.stacks right)) ∧
      (∀ i : Fin 13, 8 ≤ i.val → e.regs i = d.regs i) := by
  let a := copied left 5 d
  let b := copied right 7 a
  have ha8 : a.stacks 8 = [] := by simpa [a, copied, StackRoutines.copyStacks] using h8
  have har : a.stacks right = d.stacks right := by simp [a, copied, StackRoutines.copyStacks, hr.1]
  have hb5 : b.stacks 5 = d.stacks left := by simp [b, a, copied, StackRoutines.copyStacks, h5]
  have hb7 : b.stacks 7 = d.stacks right := by
    simp [b, a, copied, StackRoutines.copyStacks, hr.1, h7]
  obtain ⟨e, he, hresult, hregs, hstacks, he5, he7⟩ :=
    Tuple.compare_eval 5 7 (by decide) b
  refine ⟨(7 * (d.stacks left).length + 5) + ((7 * (a.stacks right).length + 5) +
    (10 * max (b.stacks 5).length (b.stacks 7).length + 6)), ?_, e, ?_, ?_, ?_, ?_⟩
  · rw [har, hb5, hb7]
    have hmax := max_le
      (Nat.le_add_right (d.stacks left).length (d.stacks right).length)
      (Nat.le_add_left (d.stacks right).length (d.stacks left).length)
    omega
  · exact Eval.seq (copy_eval left 5 d hl.1 hl.2.2 (by decide) h8)
      (Eval.seq (copy_eval right 7 a hr.2.1 hr.2.2 (by decide) ha8) he)
  · funext i
    by_cases hi5 : i = 5
    · subst i; exact he5.trans h5.symm
    by_cases hi7 : i = 7
    · subst i; exact he7.trans h7.symm
    simpa [b, a, copied, StackRoutines.copyStacks, hi5, hi7] using hstacks i hi5 hi7
  · simpa [hb5, hb7] using hresult
  · intro i hi
    have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
    have hi1 : i ≠ 1 := by intro h; subst i; simp at hi
    simpa [b, a, copied, readRegs, hi0, hi1] using hregs i hi

def numericEq (expected : Fin 2) : Cmd 13 9 :=
  .seq (less 6 (expectedPort expected))
    (.seq (RecordPrograms.atom (.copy 12 0))
      (.seq (less (expectedPort expected) 6)
        (.seq (RecordPrograms.atom (.bor 4 12 0)) (RecordPrograms.atom (.bnot 4 4)))))

/-- Numeric equality tolerates leading zero padding in the supplied bound.
Both comparisons consume only real copies of the preserved operands. -/
theorem numericEq_eval (expected : Fin 2) (d : Data)
    (h5 : d.stacks 5 = []) (h7 : d.stacks 7 = []) (h8 : d.stacks 8 = []) :
    ∃ n ≤ 50 * ((d.stacks 6).length + (d.stacks (expectedPort expected)).length + 1),
      ∃ e : Data, Eval (numericEq expected) n d e ∧ e.stacks = d.stacks ∧
        e.regs 4 = decide (toNat (d.stacks 6) = toNat (d.stacks (expectedPort expected))) ∧
        (∀ i : Fin 13, 8 ≤ i.val → i ≠ 12 → e.regs i = d.regs i) := by
  have hp : expectedPort expected ≠ 5 ∧ expectedPort expected ≠ 7 ∧ expectedPort expected ≠ 8 := by
    fin_cases expected <;> decide
  obtain ⟨n, hn, a, ha, hast, ha0, hareg⟩ := less_eval 6 (expectedPort expected) d
    (by decide) hp h5 h7 h8
  let b := (StructuredProgram.Atom.copy (r := 13) (s := 9) 12 0).eval a
  have hbst : b.stacks = d.stacks := hast
  have hb12 : b.regs 12 = decide (toNat (d.stacks 6) < toNat (d.stacks (expectedPort expected))) := by
    simpa [b, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using ha0
  obtain ⟨m, hm, c, hc, hcst, hc0, hcreg⟩ := less_eval (expectedPort expected) 6 b hp
    (by decide) (by simpa only [hbst] using h5)
    (by simpa only [hbst] using h7) (by simpa only [hbst] using h8)
  let e := (StructuredProgram.Atom.bnot (r := 13) (s := 9) 4 4).eval
    ((StructuredProgram.Atom.bor (r := 13) (s := 9) 4 12 0).eval c)
  have hc12 : c.regs 12 = decide (toNat (d.stacks 6) < toNat (d.stacks (expectedPort expected))) :=
    (hcreg 12 (by decide)).trans hb12
  have hbool (a b : ℕ) : (!(decide (a < b) || decide (b < a))) = decide (a = b) := by
    apply Bool.eq_iff_iff.mpr
    simp
    omega
  refine ⟨n + (1 + (m + (1 + 1))), ?_, e, ?_, hcst.trans hbst, ?_, ?_⟩
  · rw [hbst] at hm
    omega
  · exact Eval.seq ha (Eval.seq (.base (.atom _ _))
      (Eval.seq hc (Eval.seq (.base (.atom _ _)) (.base (.atom _ _)))))
  · simp [e, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr,
      hc12, hc0, hbst, hbool]
  · intro i hi hne
    have hi4 : i ≠ 4 := by
      intro h
      subst i
      change 8 ≤ 4 at hi
      omega
    have hci := hcreg i hi
    have hai := hareg i hi
    simpa [e, b, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr,
      hi4, hne, hai] using hci

def countTest (expected : Fin 2) : Cmd 13 9 :=
  .seq (.call countProgram) (.seq toBinary (.seq (numericEq expected) (clear 6)))

/-- Count the actual records, convert the count, compare it with a supplied
binary word, and clear every temporary. Only the scanned input is consumed. -/
theorem countTest_eval (expected : Fin 2) (records : List (List Bool)) (d : Data)
    (hin : d.stacks 5 = Encoding.encodeList id records)
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = []) (h8 : d.stacks 8 = []) :
    ∃ n ≤ 200 * ((Encoding.encodeList id records).length +
      (d.stacks (expectedPort expected)).length + 1) ^ 2, ∃ e : Data,
      Eval (countTest expected) n d e ∧ e.stacks = Function.update d.stacks 5 [] ∧
      e.regs 4 = decide (records.length = toNat (d.stacks (expectedPort expected))) ∧
      (∀ i : Fin 13, 8 ≤ i.val → i ≠ 12 → e.regs i = d.regs i) := by
  let a := counted records d
  have ha7 : a.stacks 7 = Encoding.encodeNat records.length := by simp [a, counted]
  have ha5 : a.stacks 5 = [] := by simp [a, counted]
  have ha6 : a.stacks 6 = [] := by simpa [a, counted] using h6
  have ha8 : a.stacks 8 = [] := by simpa [a, counted] using h8
  obtain ⟨n, hn, bits, b, hb, hvalue, hlength, hbst, hbreg⟩ :=
    toBinary_eval records.length a ha7 ha5 ha6 ha8
  have hb5 : b.stacks 5 = [] := by simp [hbst, a, counted]
  have hb6 : b.stacks 6 = bits := by simp [hbst]
  have hb7 : b.stacks 7 = [] := by simp [hbst]
  have hb8 : b.stacks 8 = [] := by simpa [hbst, a, counted] using h8
  have hbexpected : b.stacks (expectedPort expected) = d.stacks (expectedPort expected) := by
    fin_cases expected <;> simp [expectedPort, hbst, a, counted]
  obtain ⟨m, hm, c, hc, hcst, hc4, hcreg⟩ := numericEq_eval expected b hb5 hb7 hb8
  let e := cleared 6 c
  have hm' : m ≤ 50 * (bits.length + (d.stacks (expectedPort expected)).length + 1) := by
    simpa [hb6, hbexpected] using hm
  have hc6 : c.stacks 6 = bits := by simpa [hcst] using hb6
  refine ⟨SubexpSunflowerProgram.CountRecords.steps records +
    (n + (m + (2 * (c.stacks 6).length + 3))), ?_, e,
    Eval.seq (count_eval records d hin h7) (Eval.seq hb (Eval.seq hc (clear_eval 6 c))),
    ?_, ?_, ?_⟩
  · rw [hc6]
    have hcount := SubexpSunflowerProgram.CountRecords.steps_le_encoded records
    have hrecords := Encoding.length_encodeList_lower id records
    have hrecords' : records.length ≤ (Encoding.encodeList id records).length := by omega
    have hquad := Nat.mul_le_mul hrecords' hrecords'
    have hbits : bits.length ≤ (Encoding.encodeList id records).length :=
      hlength.trans hrecords'
    have hsum : bits.length + (d.stacks (expectedPort expected)).length + 1 ≤
        (Encoding.encodeList id records).length +
          (d.stacks (expectedPort expected)).length + 1 := by omega
    have hsumquad := Nat.mul_le_mul hsum hsum
    rw [FrontendProgram.initializeBound_eq] at hn
    let H := (Encoding.encodeList id records).length +
      (d.stacks (expectedPort expected)).length + 1
    have hH : 1 ≤ H := by dsimp [H]; omega
    have hEH : (Encoding.encodeList id records).length ≤ H := by dsimp [H]; omega
    have hRH : records.length ≤ H := hrecords'.trans hEH
    have hBH : bits.length ≤ H := hbits.trans hEH
    have hsq : H ≤ H ^ 2 := by
      rw [pow_two]
      exact Nat.le_mul_of_pos_right _ hH
    have hRsq : records.length ^ 2 ≤ H ^ 2 := Nat.pow_le_pow_left hRH 2
    have hcount' : SubexpSunflowerProgram.CountRecords.steps records ≤ 7 * H ^ 2 := by
      have h7 := Nat.mul_le_mul_left 7 hsq
      omega
    have hn' : n ≤ 32 * H ^ 2 := by
      have h8 := Nat.mul_le_mul_left 8 hRsq
      have h14 := Nat.mul_le_mul_left 14 (hRH.trans hsq)
      have h10 : 10 ≤ 10 * H ^ 2 := by omega
      omega
    have hm'' : m ≤ 50 * H ^ 2 := by
      have hmH : m ≤ 50 * H := hm'.trans (Nat.mul_le_mul_left 50 (by
        dsimp [H]
        exact hsum))
      exact hmH.trans (Nat.mul_le_mul_left 50 hsq)
    have hclear : 2 * bits.length + 3 ≤ 5 * H ^ 2 := by
      have h5 := Nat.mul_le_mul_left 5 hsq
      omega
    change SubexpSunflowerProgram.CountRecords.steps records +
        (n + (m + (2 * bits.length + 3))) ≤ 200 * H ^ 2
    omega
  · funext i
    fin_cases i <;> simp [e, cleared, StackRoutines.clearStacks, hcst, hbst, a, counted, h6, h7]
  · simpa [e, cleared, readRegs, hb6, hbexpected, hvalue] using hc4
  · intro i hi hne
    have hi3 : 3 ≤ i.val := by omega
    have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
    have hi1 : i ≠ 1 := by intro h; subst i; simp at hi
    have hh := (hcreg i hi hne).trans (hbreg i hi3)
    simpa [e, cleared, readRegs, a, counted, hi0, hi1] using hh

end Count

namespace FrameWriter

def triple {α : Type*} (a b c : α) : Fin 3 → α :=
  fun i => if i = 0 then a else if i = 1 then b else c

@[simp] theorem triple_zero {α : Type*} (a b c : α) : triple a b c 0 = a := rfl
@[simp] theorem triple_one {α : Type*} (a b c : α) : triple a b c 1 = b := rfl
@[simp] theorem triple_two {α : Type*} (a b c : α) : triple a b c 2 = c := rfl

@[simp] theorem update_triple_zero {α : Type*} (a b c d : α) :
    Function.update (triple a b c) 0 d = triple d b c := by
  funext i
  fin_cases i <;> simp [triple]

@[simp] theorem update_triple_one {α : Type*} (a b c d : α) :
    Function.update (triple a b c) 1 d = triple a d c := by
  funext i
  fin_cases i <;> simp [triple]

@[simp] theorem update_triple_two {α : Type*} (a b c d : α) :
    Function.update (triple a b c) 2 d = triple a b d := by
  funext i
  fin_cases i <;> simp [triple]

def quadruple {α : Type*} (a b c d : α) : Fin 4 → α :=
  fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d

@[simp] theorem quadruple_zero {α : Type*} (a b c d : α) : quadruple a b c d 0 = a := rfl
@[simp] theorem quadruple_one {α : Type*} (a b c d : α) : quadruple a b c d 1 = b := rfl
@[simp] theorem quadruple_two {α : Type*} (a b c d : α) : quadruple a b c d 2 = c := rfl
@[simp] theorem quadruple_three {α : Type*} (a b c d : α) : quadruple a b c d 3 = d := rfl

@[simp] theorem update_quadruple_zero {α : Type*} (a b c d e : α) :
    Function.update (quadruple a b c d) 0 e = quadruple e b c d := by
  funext i; fin_cases i <;> simp [quadruple]
@[simp] theorem update_quadruple_one {α : Type*} (a b c d e : α) :
    Function.update (quadruple a b c d) 1 e = quadruple a e c d := by
  funext i; fin_cases i <;> simp [quadruple]
@[simp] theorem update_quadruple_two {α : Type*} (a b c d e : α) :
    Function.update (quadruple a b c d) 2 e = quadruple a b e d := by
  funext i; fin_cases i <;> simp [quadruple]
@[simp] theorem update_quadruple_three {α : Type*} (a b c d e : α) :
    Function.update (quadruple a b c d) 3 e = quadruple a b c e := by
  funext i; fin_cases i <;> simp [quadruple]

def cfg4 {l : ℕ} (pc : Option (Fin l)) (value present operation : Bool)
    (code depth operands scratch : List Bool) : Cfg 3 4 l :=
  ⟨pc, triple value present operation, quadruple code depth operands scratch⟩

def parserRegister : Fin 2 → Fin 3 := Fin.castAdd 1
def parserStack (i : Fin 2) : Fin 4 := if i = 0 then 0 else 3
def parserLabel : Fin 7 → Fin 17 := Fin.castAdd 10

theorem parserRegister_injective : Function.Injective parserRegister := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 3 => i.val) h)

theorem parserStack_injective : Function.Injective parserStack := by decide

/-- The first seven labels are the actual relocated frame parser. The remaining
labels rebuild the escaped payload from its reverse and add the list cons tag. -/
def literalService : Program 3 4 17 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code := Fin.addCases (motive := fun _ : Fin (7 + 10) => Instr 3 4 17)
    (fun pc : Fin 7 => ProgramLinking.relocateInstr parserRegister parserStack parserLabel
      (some 7) (ParserProgram.frameProgram.code pc))
    (fun pc : Fin 10 => match pc.val with
      | 0 => .set 0 false 8
      | 1 => .push 2 0 9
      | 2 => .pop 3 0 1 10
      | 3 => .branch 1 11 14
      | 4 => .push 2 0 12
      | 5 => .set 0 true 13
      | 6 => .push 2 0 9
      | 7 => .set 0 true 15
      | 8 => .push 2 0 16
      | _ => .halt)

@[simp] private theorem literalService_code7 : literalService.code 7 = .set 0 false 8 := rfl
@[simp] private theorem literalService_code8 : literalService.code 8 = .push 2 0 9 := rfl
@[simp] private theorem literalService_code9 : literalService.code 9 = .pop 3 0 1 10 := rfl
@[simp] private theorem literalService_code10 : literalService.code 10 = .branch 1 11 14 := rfl
@[simp] private theorem literalService_code11 : literalService.code 11 = .push 2 0 12 := rfl
@[simp] private theorem literalService_code12 : literalService.code 12 = .set 0 true 13 := rfl
@[simp] private theorem literalService_code13 : literalService.code 13 = .push 2 0 9 := rfl
@[simp] private theorem literalService_code14 : literalService.code 14 = .set 0 true 15 := rfl
@[simp] private theorem literalService_code15 : literalService.code 15 = .push 2 0 16 := rfl
@[simp] private theorem literalService_code16 : literalService.code 16 = .halt := rfl

/-- Escaped data without the final false delimiter. -/
def escapeBits : List Bool → List Bool
  | [] => []
  | b :: bs => true :: b :: escapeBits bs

theorem escapeBits_append (a b : List Bool) :
    escapeBits (a ++ b) = escapeBits a ++ escapeBits b := by
  induction a with
  | nil => rfl
  | cons a as ih => simp [escapeBits, ih]

theorem frame_eq_escape (bits : List Bool) :
    Encoding.frame bits = escapeBits bits ++ [false] := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
      rw [Encoding.frame_cons, escapeBits, ih]
      simp only [List.cons_append]

theorem literalService_encode_cycle (b v p op : Bool) (code depth operands scratch : List Bool) :
    Trace literalService 5
      (cfg4 (some 9) v p op code depth operands (b :: scratch))
      (cfg4 (some 9) true true op code depth (true :: b :: operands) scratch) := by
  refine .cons (b := cfg4 (some 10) b true op code depth operands scratch) ?_ ?_
  · simp [step, execInstr, cfg4, readRegs]
  refine .cons (b := cfg4 (some 11) b true op code depth operands scratch) ?_ ?_
  · simp [step, execInstr, cfg4]
  refine .cons (b := cfg4 (some 12) b true op code depth (b :: operands) scratch) ?_ ?_
  · simp [step, execInstr, cfg4]
  refine .cons (b := cfg4 (some 13) true true op code depth (b :: operands) scratch) ?_ ?_
  · simp [step, execInstr, cfg4]
  refine .cons ?_ (.refl _)
  simp [step, execInstr, cfg4]

theorem literalService_encode_loop (scratch code depth operands : List Bool) (v p op : Bool) :
    Trace literalService (5 * scratch.length + 2)
      (cfg4 (some 9) v p op code depth operands scratch)
      (cfg4 (some 14) false false op code depth (escapeBits scratch.reverse ++ operands) []) := by
  induction scratch generalizing operands v p with
  | nil =>
      refine .cons (b := cfg4 (some 10) false false op code depth operands []) ?_ ?_
      · simp [step, execInstr, cfg4, readRegs]
      · refine .cons ?_ (.refl _)
        simp [step, execInstr, cfg4, escapeBits]
  | cons b bs ih =>
      have h := (literalService_encode_cycle b v p op code depth operands bs).trans
        (ih (true :: b :: operands) true true)
      have hn : 5 + (5 * bs.length + 2) = 5 * (b :: bs).length + 2 := by
        simp only [List.length_cons]
        omega
      simpa only [hn, List.reverse_cons, escapeBits_append, escapeBits,
        List.append_assoc, List.cons_append, List.nil_append] using h

theorem literalService_encode_trace (bits code depth operands : List Bool) (v p op : Bool) :
    Trace literalService (5 * bits.length + 7)
      (cfg4 (some 7) v p op code depth operands bits.reverse)
      (cfg4 none true false op code depth (true :: (Encoding.frame bits ++ operands)) []) := by
  have init : Trace literalService 2
      (cfg4 (some 7) v p op code depth operands bits.reverse)
      (cfg4 (some 9) false p op code depth (false :: operands) bits.reverse) := by
    refine .cons (b := cfg4 (some 8) false p op code depth operands bits.reverse) ?_ ?_
    · simp [step, execInstr, cfg4]
    · refine .cons ?_ (.refl _)
      simp [step, execInstr, cfg4]
  have loop := literalService_encode_loop bits.reverse code depth (false :: operands) false p op
  have finish : Trace literalService 3
      (cfg4 (some 14) false false op code depth (Encoding.frame bits ++ operands) [])
      (cfg4 none true false op code depth (true :: (Encoding.frame bits ++ operands)) []) := by
    refine .cons (b := cfg4 (some 15) true false op code depth (Encoding.frame bits ++ operands) []) ?_ ?_
    · simp [step, execInstr, cfg4]
    refine .cons (b := cfg4 (some 16) true false op code depth (true :: (Encoding.frame bits ++ operands)) []) ?_ ?_
    · simp [step, execInstr, cfg4]
    refine .cons ?_ (.refl _)
    simp [step, execInstr, cfg4]
  have loop' : Trace literalService (5 * bits.length + 2)
      (cfg4 (some 9) false p op code depth (false :: operands) bits.reverse)
      (cfg4 (some 14) false false op code depth (Encoding.frame bits ++ operands) []) := by
    simpa [List.length_reverse, List.reverse_reverse, frame_eq_escape,
      List.append_assoc] using loop
  have h := (init.trans loop').trans finish
  have hn : 2 + (5 * bits.length + 2) + 3 = 5 * bits.length + 7 := by omega
  simpa only [hn] using h


end FrameWriter

namespace Filter

def filterState (value present selected : Bool)
    (source work output payload : List Bool) : StructuredProgram.State 3 4 :=
  ⟨FrameWriter.triple value present selected,
    FrameWriter.quadruple source work output payload⟩

/-- Enter the proved frame writer directly at its fixed encoding entry. -/
def emitRecordProgram : Program 3 4 17 :=
  { FrameWriter.literalService with inputStack := 3, entry := 7 }

theorem emitRecord_trace (bits source work output : List Bool) (v p selected : Bool) :
    Trace emitRecordProgram (5 * bits.length + 7)
      ((filterState v p selected source work output bits.reverse).withPC
        (some emitRecordProgram.entry))
      ((filterState true false selected source work
        (true :: (Encoding.frame bits ++ output)) []).withPC none) := by
  simpa only [emitRecordProgram, step, filterState, StructuredProgram.State.withPC,
    FrameWriter.cfg4] using
    FrameWriter.literalService_encode_trace bits source work output v p selected

def discardRecordProgram : Program 3 4 3 := StackRoutines.clearProgram 3 0 1

theorem discardRecord_trace (bits source work output : List Bool) (v p selected : Bool) :
    Trace discardRecordProgram (2 * bits.length + 3)
      ((filterState v p selected source work output bits.reverse).withPC
        (some discardRecordProgram.entry))
      ((filterState false false selected source work output []).withPC none) := by
  have h := StackRoutines.clearProgram_trace (r := 3) (s := 4) 3 0 1
    (FrameWriter.triple v p selected)
    (FrameWriter.quadruple source work output bits.reverse)
  have hh := StackRoutines.halt_after_trace (StackRoutines.clearProgram (3 : Fin 4)
    (0 : Fin 3) 1) h 2 rfl rfl
  simpa [discardRecordProgram, StackRoutines.clearProgram, StackRoutines.clearResult,
    StackRoutines.clearStacks, filterState, StructuredProgram.State.withPC,
    readRegs, Nat.add_assoc] using hh

def resetFilterFlags : StructuredProgram.Cmd 3 4 :=
  .seq (.atom (.set 0 false)) (.seq (.atom (.set 1 true)) (.atom (.set 2 false)))

theorem resetFilterFlags_eval (v p selected : Bool)
    (source work output payload : List Bool) :
    StructuredProgram.Eval resetFilterFlags 3
      (filterState v p selected source work output payload)
      (filterState false true false source work output payload) := by
  have h0 : StructuredProgram.Eval (.atom (.set 0 false)) 1
      (filterState v p selected source work output payload)
      (filterState false p selected source work output payload) := by
    simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr,
      filterState] using StructuredProgram.Eval.atom (.set 0 false)
        (filterState v p selected source work output payload)
  have h1 : StructuredProgram.Eval (.atom (.set 1 true)) 1
      (filterState false p selected source work output payload)
      (filterState false true selected source work output payload) := by
    simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr,
      filterState] using StructuredProgram.Eval.atom (.set 1 true)
        (filterState false p selected source work output payload)
  have h2 : StructuredProgram.Eval (.atom (.set 2 false)) 1
      (filterState false true selected source work output payload)
      (filterState false true false source work output payload) := by
    simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr,
      filterState] using StructuredProgram.Eval.atom (.set 2 false)
        (filterState false true selected source work output payload)
  exact .seq h0 (.seq h1 h2)

def emitIfSelected : StructuredCalls.Cmd 3 4 :=
  .seq (.ite 2 (.call emitRecordProgram) (.call discardRecordProgram))
    (.base resetFilterFlags)

def emitIfSelectedSteps (selected : Bool) (bits : List Bool) : ℕ :=
  if selected then 5 * bits.length + 11 else 2 * bits.length + 7

/-- An actual measured branch: the kept record is encoded, and an omitted
record is consumed. Both paths leave the callback ready for the next record. -/
theorem emitIfSelected_eval (selected : Bool)
    (bits source work output : List Bool) (v p : Bool) :
    StructuredCalls.Eval emitIfSelected (emitIfSelectedSteps selected bits)
      (filterState v p selected source work output bits.reverse)
      (filterState false true false source work
        (if selected then true :: (Encoding.frame bits ++ output) else output) []) := by
  cases selected with
  | false =>
      have hc := StructuredCalls.Eval.call discardRecordProgram
        (discardRecord_trace bits source work output v p false)
      have hi := StructuredCalls.Eval.ite_false (yes := .call emitRecordProgram)
        (test := (2 : Fin 3)) (by rfl) hc
      have hs := hi.seq (StructuredCalls.Eval.base
        (resetFilterFlags_eval false false false source work output []))
      simpa [emitIfSelected, emitIfSelectedSteps, Nat.add_assoc] using hs
  | true =>
      have hc := StructuredCalls.Eval.call emitRecordProgram
        (emitRecord_trace bits source work output v p true)
      have hi := StructuredCalls.Eval.ite_true (no := .call discardRecordProgram)
        (test := (2 : Fin 3)) (by rfl) hc
      have hs := hi.seq (StructuredCalls.Eval.base
        (resetFilterFlags_eval true false true source work
          (true :: (Encoding.frame bits ++ output)) []))
      simpa [emitIfSelected, emitIfSelectedSteps, Nat.add_assoc] using hs

def emitIfSelectedProgram := StructuredCalls.compiled emitIfSelected 3 2

theorem emitIfSelected_trace (selected : Bool)
    (bits source work output : List Bool) (v p : Bool) :
    Trace emitIfSelectedProgram (emitIfSelectedSteps selected bits + 1)
      ((filterState v p selected source work output bits.reverse).withPC
        (some emitIfSelectedProgram.entry))
      ((filterState false true false source work
        (if selected then true :: (Encoding.frame bits ++ output) else output) []).withPC none) :=
  StructuredCalls.compiled_halt_trace
    (emitIfSelected_eval selected bits source work output v p) 3 2

theorem emitIfSelected_steps_le (selected : Bool) (bits : List Bool) :
    emitIfSelectedSteps selected bits + 1 ≤ 5 * bits.length + 12 := by
  unfold emitIfSelectedSteps
  split <;> omega

@[simp] theorem unread_false (records : List (List Bool)) (suffix : List Bool) :
    RecordPrograms.unread (fun _ => false) records suffix = suffix := by
  induction records with
  | nil => rfl
  | cons bits records ih => simpa [RecordPrograms.unread] using ih

structure FilterEffect {r s : ℕ} (output : Fin s) (keep : List Bool → Bool)
    (bits : List Bool) (before after : StructuredProgram.State r s) : Prop where
  output_eq : after.stacks output =
    if keep bits then true :: (Encoding.frame bits ++ before.stacks output)
    else before.stacks output

theorem filterVisits_result {r s : ℕ} (output : Fin s) (keep : List Bool → Bool)
    {records : List (List Bool)} {before after : StructuredProgram.State r s}
    (h : RecordPrograms.Visits (fun _ => false) (FilterEffect output keep)
      records before after)
    (acc : List (List Bool)) (hacc : before.stacks output = Encoding.encodeList id acc) :
    after.stacks output = Encoding.encodeList id ((records.filter keep).reverse ++ acc) := by
  induction h generalizing acc with
  | nil base => simpa using hacc
  | hit ht _ => cases ht
  | @miss bits records before middle after _ he _ ih =>
      cases hkeep : keep bits with
      | false =>
          have hm : middle.stacks output = Encoding.encodeList id acc := by
            simpa [hkeep, hacc] using he.output_eq
          simpa [List.filter_cons, hkeep] using ih acc hm
      | true =>
          have hm : middle.stacks output = Encoding.encodeList id (bits :: acc) := by
            simpa [hkeep, hacc, Encoding.encodeList] using he.output_eq
          simpa [List.filter_cons, hkeep, List.reverse_cons, List.append_assoc] using
            ih (bits :: acc) hm


end Filter

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives
