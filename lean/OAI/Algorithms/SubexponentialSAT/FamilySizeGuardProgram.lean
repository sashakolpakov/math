import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.TupleGuardProgram
import OAI.Algorithms.SubexponentialSAT.FrontendProgram
import OAI.Algorithms.SubexponentialSAT.SubexpSunflowerProgram
import OAI.Algorithms.SubexponentialSAT.RecordMappedPrograms
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-!
# Binary size and width guards for selected clause families

The family is a nested framed record list. Supplied width and family-size
thresholds are little-endian binary words. Counts produced from the actual
input are converted by a checked finite program; supplied thresholds are never
expanded to unary.
-/

namespace SubexponentialSAT.FamilySizeGuardProgram

open BitProgram StructuredCalls BinaryArithmetic
open TupleGuardProgram (Data copied copy copy_eval moved move move_eval cleared clear clear_eval)

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

abbrev reset : Cmd 13 9 :=
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
abbrev toBinary : Cmd 13 9 := .seq reset (.call binaryProgram)

/-- Convert an input-sized unary record count to binary. The cost comes from
the actual header parser and dynamic binary length counter. -/
theorem toBinary_eval (n : ℕ) (d : Data) (h7 : d.stacks 7 = Encoding.encodeNat n)
    (h5 : d.stacks 5 = []) (h6 : d.stacks 6 = []) (h8 : d.stacks 8 = []) :
    ∃ t ≤ FrontendProgram.initializeBound n + 3, ∃ bits : List Bool, ∃ e : Data,
      Eval toBinary t d e ∧ BinaryArithmetic.toNat bits = n ∧ bits.length ≤ n ∧
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
    · calc
        e.stacks _ = e.stacks (binaryStack 1) := congrArg e.stacks (Fin.ext rfl)
        _ = b.stacks 1 := hs 1
        _ = [] := by
          simp [b, FrontendProgram.cfg, FrontendProgram.storage,
            StructuredProgram.State.ofCfg ]
        _ = Function.update (Function.update d.stacks 7 []) 6 bits _ := by
          simp [h5]
    · change e.stacks (binaryStack 2) = bits
      rw [hs 2]
      simp [b, FrontendProgram.cfg, FrontendProgram.storage,
        StructuredProgram.State.ofCfg]
    · change e.stacks (binaryStack 0) = []
      rw [hs 0]
      simp [b, FrontendProgram.cfg, FrontendProgram.storage,
        StructuredProgram.State.ofCfg]
    · calc
        e.stacks _ = e.stacks (binaryStack 3) := congrArg e.stacks (Fin.ext rfl)
        _ = b.stacks 3 := hs 3
        _ = [] := by
          simp [b, FrontendProgram.cfg, FrontendProgram.storage,
            StructuredProgram.State.ofCfg ]
        _ = Function.update (Function.update d.stacks 7 []) 6 bits _ := by
          simp [h8]
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

abbrev less (left right : Fin 9) : Cmd 13 9 :=
  .seq (copy left 5) (.seq (copy right 7) (TupleGuardProgram.compare 5 7))

theorem less_eval (left right : Fin 9) (d : Data)
    (hl : left ≠ 5 ∧ left ≠ 7 ∧ left ≠ 8)
    (hr : right ≠ 5 ∧ right ≠ 7 ∧ right ≠ 8)
    (h5 : d.stacks 5 = []) (h7 : d.stacks 7 = []) (h8 : d.stacks 8 = []) :
    ∃ n ≤ 20 * ((d.stacks left).length + (d.stacks right).length + 1), ∃ e : Data,
      Eval (less left right) n d e ∧ e.stacks = d.stacks ∧
      e.regs 0 = decide (BinaryArithmetic.toNat (d.stacks left) < BinaryArithmetic.toNat (d.stacks right)) ∧
      (∀ i : Fin 13, 8 ≤ i.val → e.regs i = d.regs i) := by
  let a := copied left 5 d
  let b := copied right 7 a
  have ha8 : a.stacks 8 = [] := by simpa [a, copied, StackRoutines.copyStacks] using h8
  have har : a.stacks right = d.stacks right := by simp [a, StackRoutines.copyStacks, hr.1]
  have hb5 : b.stacks 5 = d.stacks left := by simp [b, a, StackRoutines.copyStacks, h5]
  have hb7 : b.stacks 7 = d.stacks right := by
    simp [b, a, StackRoutines.copyStacks, hr.1, h7]
  obtain ⟨e, he, hresult, hregs, hstacks, he5, he7⟩ :=
    TupleGuardProgram.compare_eval 5 7 (by decide) b
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

abbrev numericEq (expected : Fin 2) : Cmd 13 9 :=
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
        e.regs 4 = decide (BinaryArithmetic.toNat (d.stacks 6) = BinaryArithmetic.toNat (d.stacks (expectedPort expected))) ∧
        (∀ i : Fin 13, 8 ≤ i.val → i ≠ 12 → e.regs i = d.regs i) := by
  have hp : expectedPort expected ≠ 5 ∧ expectedPort expected ≠ 7 ∧ expectedPort expected ≠ 8 := by
    fin_cases expected <;> decide
  obtain ⟨n, hn, a, ha, hast, ha0, hareg⟩ := less_eval 6 (expectedPort expected) d
    (by decide) hp h5 h7 h8
  let b := (StructuredProgram.Atom.copy (r := 13) (s := 9) 12 0).eval a
  have hbst : b.stacks = d.stacks := hast
  have hb12 : b.regs 12 = decide (BinaryArithmetic.toNat (d.stacks 6) < BinaryArithmetic.toNat (d.stacks (expectedPort expected))) := by
    simpa [b, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using ha0
  obtain ⟨m, hm, c, hc, hcst, hc0, hcreg⟩ := less_eval (expectedPort expected) 6 b hp
    (by decide) (by simpa only [hbst] using h5)
    (by simpa only [hbst] using h7) (by simpa only [hbst] using h8)
  let e := (StructuredProgram.Atom.bnot (r := 13) (s := 9) 4 4).eval
    ((StructuredProgram.Atom.bor (r := 13) (s := 9) 4 12 0).eval c)
  have hc12 : c.regs 12 = decide (BinaryArithmetic.toNat (d.stacks 6) < BinaryArithmetic.toNat (d.stacks (expectedPort expected))) :=
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
  · simp [e, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr,
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

abbrev countTest (expected : Fin 2) : Cmd 13 9 :=
  .seq (.call countProgram) (.seq toBinary (.seq (numericEq expected) (clear 6)))

/-- Count the actual records, convert the count, compare it with a supplied
binary word, and clear every temporary. Only the scanned input is consumed. -/
theorem countTest_eval (expected : Fin 2) (records : List (List Bool)) (d : Data)
    (hin : d.stacks 5 = Encoding.encodeList id records)
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = []) (h8 : d.stacks 8 = []) :
    ∃ n ≤ 200 * ((Encoding.encodeList id records).length +
      (d.stacks (expectedPort expected)).length + 1) ^ 2, ∃ e : Data,
      Eval (countTest expected) n d e ∧ e.stacks = Function.update d.stacks 5 [] ∧
      e.regs 4 = decide (records.length = BinaryArithmetic.toNat (d.stacks (expectedPort expected))) ∧
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
    fin_cases i <;> simp [e, StackRoutines.clearStacks, hcst, hbst, a, counted, h6, h7]
  · simpa [e, cleared, readRegs, hb6, hbexpected, hvalue] using hc4
  · intro i hi hne
    have hi3 : 3 ≤ i.val := by omega
    have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
    have hi1 : i ≠ 1 := by intro h; subst i; simp at hi
    have hh := (hcreg i hi hne).trans (hbreg i hi3)
    simpa [e, cleared, readRegs, a, counted, hi0, hi1] using hh

abbrev Clause := List (List Bool)
abbrev Family := List Clause

def clauseCode (C : Clause) : List Bool := Encoding.encodeList id C
def familyCode (G : Family) : List Bool := Encoding.encodeList clauseCode G

theorem encodeFamily_eq (G : Family) : Encoding.encodeList id (G.map clauseCode) = familyCode G := by
  induction G with
  | nil => rfl
  | cons C G ih => simp [Encoding.encodeList, familyCode] at ih ⊢; exact ih

def invariant (original width size : List Bool) (saved : Bool) (d : Data) : Prop :=
  d.stacks 0 = original ∧ d.stacks 3 = width ∧ d.stacks 4 = size ∧ d.stacks 5 = [] ∧
    d.stacks 6 = [] ∧ d.stacks 7 = [] ∧ d.stacks 8 = [] ∧ d.regs 11 = saved

def ports : RecordPrograms.Ports 13 9 where
  tag := 8
  present := 9
  found := 10
  source := 1
  payload := 2
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

theorem invariant_state (original width size : List Bool) (saved : Bool)
    (base : Data) (v pr f : Bool) (src out : List Bool) :
    invariant original width size saved (RecordPrograms.state ports base v pr f src out) ↔
      invariant original width size saved base := by
  simp [invariant, RecordPrograms.state, ports]

abbrev widthCallback : Cmd 13 9 :=
  .seq (move 2 5) (.seq (countTest 0) (RecordPrograms.atom (.bnot 10 4)))

def widthCost (width : List Bool) (C : Clause) : ℕ :=
  300 * ((clauseCode C).length + width.length + 1) ^ 2

theorem widthCallback_eval (original width size : List Bool) (saved : Bool)
    (C : Clause) (d : Data) (hd : invariant original width size saved d)
    (hinput : d.stacks 2 = (clauseCode C).reverse) :
    ∃ n ≤ widthCost width C, ∃ e : Data, Eval widthCallback n d e ∧
      invariant original width size saved e ∧ e.stacks 1 = d.stacks 1 ∧ e.stacks 2 = [] ∧
      e.regs 8 = d.regs 8 ∧ e.regs 9 = d.regs 9 ∧
      e.regs 10 = !decide (C.length = BinaryArithmetic.toNat width) := by
  rcases hd with ⟨h0, h3, h4, h5, h6, h7, h8, h11⟩
  let a := moved 2 5 d
  have ha5 : a.stacks 5 = Encoding.encodeList id C := by
    simp [a, StackRoutines.transferStacks, hinput, h5, clauseCode]
  have ha6 : a.stacks 6 = [] := by simpa [a, moved, StackRoutines.transferStacks] using h6
  have ha7 : a.stacks 7 = [] := by simpa [a, moved, StackRoutines.transferStacks] using h7
  have ha8 : a.stacks 8 = [] := by simpa [a, moved, StackRoutines.transferStacks] using h8
  have ha3 : a.stacks (expectedPort 0) = width := by
    simpa [a, moved, StackRoutines.transferStacks, expectedPort] using h3
  obtain ⟨n, hn, b, hb, hbst, hb4, hbreg⟩ := countTest_eval 0 C a ha5 ha6 ha7 ha8
  let e := (StructuredProgram.Atom.bnot (r := 13) (s := 9) 10 4).eval b
  have he_stacks : e.stacks = Function.update d.stacks 2 [] := by
    funext i
    fin_cases i <;> simp [e, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr,
      hbst, a, StackRoutines.transferStacks, h5]
  have he_reg (i : Fin 13) (hi : 8 ≤ i.val) (hi10 : i ≠ 10) (hi12 : i ≠ 12) :
      e.regs i = d.regs i := by
    have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
    have hi1 : i ≠ 1 := by intro h; subst i; simp at hi
    simpa [e, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr,
      hi10, a, moved, readRegs, hi0, hi1] using hbreg i hi hi12
  refine ⟨(3 * (d.stacks 2).length + 3) + (n + 1), ?_, e,
    Eval.seq (move_eval 2 5 (by decide) d) (Eval.seq hb (.base (.atom _ _))),
    ?_, ?_, ?_, he_reg 8 (by decide) (by decide) (by decide),
    he_reg 9 (by decide) (by decide) (by decide), ?_⟩
  · rw [ha3] at hn
    simp only [hinput, List.length_reverse]
    dsimp [widthCost, clauseCode]
    have hpos : 1 ≤ (Encoding.encodeList id C).length + width.length + 1 := by omega
    have hsq := Nat.mul_le_mul_left
      ((Encoding.encodeList id C).length + width.length + 1) hpos
    nlinarith only [hn, hsq]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [he_stacks] using h0
    · simpa [he_stacks] using h3
    · simpa [he_stacks] using h4
    · simpa [he_stacks] using h5
    · simpa [he_stacks] using h6
    · simpa [he_stacks] using h7
    · simpa [he_stacks] using h8
    · exact (he_reg 11 (by decide) (by decide) (by decide)).trans h11
  · simp [he_stacks]
  · simp [he_stacks]
  · simp [e, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, hb4, ha3]

theorem widthCallback_contract (original width size : List Bool) (saved : Bool) :
    RecordMappedPrograms.Contract ports widthCallback clauseCode
      (fun C => !decide (C.length = BinaryArithmetic.toNat width)) (widthCost width)
      (invariant original width size saved) := by
  intro C tail base hbase
  let d := RecordPrograms.state ports base false true false tail (clauseCode C).reverse
  have hd : invariant original width size saved d :=
    (invariant_state _ _ _ _ _ _ _ _ _ _).mpr hbase
  have hin : d.stacks 2 = (clauseCode C).reverse := by simp [d, RecordPrograms.state, ports]
  obtain ⟨n, hn, e, he, hv, hs, hp, hr8, hr9, hr10⟩ :=
    widthCallback_eval original width size saved C d hd hin
  have heq : RecordPrograms.state ports e false true (!decide (C.length = BinaryArithmetic.toNat width)) tail [] = e := by
    apply RecordPrograms.state_eq_self
    · simpa [d, RecordPrograms.state, ports] using hr8
    · simpa [d, RecordPrograms.state, ports] using hr9
    · exact hr10
    · simpa [d, RecordPrograms.state, ports] using hs
    · exact hp
  refine ⟨n, e, hn, hv, ?_⟩
  rw [heq]
  exact he

theorem widthBudget_le (width : List Bool) (G : Family) :
    4 + RecordMappedPrograms.budget clauseCode (widthCost width) G ≤
      (300 * ((familyCode G).length + width.length + 1) ^ 2 + 17) *
        ((familyCode G).length + 1) := by
  have hcost : ∀ C ∈ G, widthCost width C ≤ 0 * (clauseCode C).length +
      300 * ((familyCode G).length + width.length + 1) ^ 2 := by
    intro C hC
    have hlen : (clauseCode C).length ≤ (familyCode G).length := by
      rw [← encodeFamily_eq]
      exact TupleGuardProgram.record_length_le _ _ (List.mem_map.mpr ⟨C, hC, rfl⟩)
    have hsum : (clauseCode C).length + width.length + 1 ≤
        (familyCode G).length + width.length + 1 := by omega
    have hquad := Nat.mul_le_mul hsum hsum
    dsimp [widthCost]
    nlinarith
  simpa only [Nat.zero_add, familyCode] using
    RecordMappedPrograms.program_budget_le_input clauseCode (widthCost width) G 0
      (300 * ((familyCode G).length + width.length + 1) ^ 2) hcost

def workEmpty (d : Data) : Prop :=
  d.stacks 1 = [] ∧ d.stacks 2 = [] ∧ d.stacks 5 = [] ∧
    d.stacks 6 = [] ∧ d.stacks 7 = [] ∧ d.stacks 8 = []

def saved (d : Data) : Data := (StructuredProgram.Atom.copy (r := 13) (s := 9) 11 4).eval d

def finished (d : Data) : Data :=
  (StructuredProgram.Atom.band (r := 13) (s := 9) 10 10 11).eval
    ((StructuredProgram.Atom.bnot (r := 13) (s := 9) 10 10).eval (cleared 1 d))

abbrev command : Cmd 13 9 :=
  .seq (copy 0 5) (.seq (countTest 1)
    (.seq (RecordPrograms.atom (.copy 11 4)) (.seq (copy 0 1)
      (.seq (RecordPrograms.iterate ports widthCallback)
        (.seq (clear 1) (.seq (RecordPrograms.atom (.bnot 10 10))
          (RecordPrograms.atom (.band 10 10 11))))))))

def program := compiled command 0 0

def passes (width size : List Bool) (G : Family) : Bool :=
  decide (G.length = BinaryArithmetic.toNat size) && !(G.any (fun C => !decide (C.length = BinaryArithmetic.toNat width)))

def bound (width size : List Bool) (G : Family) : ℕ :=
  200 * ((familyCode G).length + size.length + 1) ^ 2 +
    (300 * ((familyCode G).length + width.length + 1) ^ 2 + 17) *
      ((familyCode G).length + 1) + 16 * (familyCode G).length + 30

/-- Complete measured execution on the nested canonical record format. The
two supplied binary thresholds and the selected family are preserved. -/
theorem command_eval (width size : List Bool) (G : Family) (d : Data)
    (h0 : d.stacks 0 = familyCode G) (h3 : d.stacks 3 = width) (h4 : d.stacks 4 = size)
    (hw : workEmpty d) :
    ∃ n, n + 1 ≤ bound width size G ∧ ∃ e : Data, Eval command n d e ∧
      e.stacks 0 = familyCode G ∧ e.stacks 3 = width ∧ e.stacks 4 = size ∧
      workEmpty e ∧ e.regs 10 = passes width size G := by
  rcases hw with ⟨h1, h2, h5, h6, h7, h8⟩
  let a := copied 0 5 d
  have ha5 : a.stacks 5 = Encoding.encodeList id (G.map clauseCode) := by
    simp [a, StackRoutines.copyStacks, h0, h5, encodeFamily_eq]
  have ha6 : a.stacks 6 = [] := by simpa [a, copied, StackRoutines.copyStacks] using h6
  have ha7 : a.stacks 7 = [] := by simpa [a, copied, StackRoutines.copyStacks] using h7
  have ha8 : a.stacks 8 = [] := by simpa [a, copied, StackRoutines.copyStacks] using h8
  obtain ⟨n, hn, b, hb, hbst, hb4, hbreg⟩ := countTest_eval 1 (G.map clauseCode) a ha5 ha6 ha7 ha8
  have hbst' : b.stacks = d.stacks := by
    funext i
    fin_cases i <;> simp [hbst, a, StackRoutines.copyStacks, h5]
  have hb4' : b.regs 4 = decide (G.length = BinaryArithmetic.toNat size) := by
    simpa [a, copied, StackRoutines.copyStacks, expectedPort, h4] using hb4
  let c := saved b
  let s := copied 0 1 c
  have hsst : s.stacks = Function.update d.stacks 1 (familyCode G) := by
    simp [s, c, saved, StackRoutines.copyStacks, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, hbst', h0, h1]
  have hs11 : s.regs 11 = decide (G.length = BinaryArithmetic.toNat size) := by
    simp [s, readRegs, c, saved, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, hb4']
  have hsinv : invariant (familyCode G) width size (decide (G.length = BinaryArithmetic.toNat size)) s := by
    simp [invariant, hsst, h0, h3, h4, h5, h6, h7, h8, hs11]
  have hs1 : s.stacks 1 = familyCode G := by simp [hsst]
  have hs2 : s.stacks 2 = [] := by simpa [hsst] using h2
  obtain ⟨m, next, hm, hnext, he⟩ := RecordMappedPrograms.iterate_run ports widthCallback clauseCode
    (fun C => !decide (C.length = BinaryArithmetic.toNat width)) (widthCost width)
    (invariant (familyCode G) width size (decide (G.length = BinaryArithmetic.toNat size)))
    (widthCallback_contract _ _ _ _) G [] s hsinv (s.regs 8) (s.regs 9) (s.regs 10)
  have hstart : RecordPrograms.state ports s (s.regs 8) (s.regs 9) (s.regs 10)
      (Encoding.encodeList clauseCode G ++ []) [] = s := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · rw [show ports.source = (1 : Fin 9) from rfl]
      simpa only [familyCode, List.append_nil] using hs1
    · exact hs2
  rw [hstart] at he
  let q := RecordPrograms.state ports next false true
    (G.any (fun C => !decide (C.length = BinaryArithmetic.toNat width)))
    (RecordMappedPrograms.unread clauseCode (fun C => !decide (C.length = BinaryArithmetic.toNat width)) G []) []
  have hqinv : invariant (familyCode G) width size (decide (G.length = BinaryArithmetic.toNat size)) q :=
    (invariant_state _ _ _ _ _ _ _ _ _ _).mpr hnext
  have hq1 : (q.stacks 1).length ≤ (familyCode G).length := by
    simpa [q, RecordPrograms.state, ports, familyCode] using
      RecordMappedPrograms.unread_length_le clauseCode
        (fun C => !decide (C.length = BinaryArithmetic.toNat width)) G []
  have hq2 : q.stacks 2 = [] := by simp [q, RecordPrograms.state, ports]
  have hq10 : q.regs 10 = G.any (fun C => !decide (C.length = BinaryArithmetic.toNat width)) := by
    simp [q, RecordPrograms.state, ports]
  have hq11 : q.regs 11 = decide (G.length = BinaryArithmetic.toNat size) := hqinv.2.2.2.2.2.2.2
  have hc0 : c.stacks 0 = familyCode G := by
    simpa [c, saved, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr, hbst'] using h0
  have hc8 : c.stacks 8 = [] := by
    simpa [c, saved, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr, hbst'] using h8
  refine ⟨(7 * (d.stacks 0).length + 5) + (n + (1 +
    ((7 * (c.stacks 0).length + 5) + (m + ((2 * (q.stacks 1).length + 3) + (1 + 1)))))),
    ?_, finished q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hn' : n ≤ 200 * ((familyCode G).length + size.length + 1) ^ 2 := by
      simpa [encodeFamily_eq, a, copied, StackRoutines.copyStacks, expectedPort, h4] using hn
    have hbudget := widthBudget_le width G
    rw [h0, hc0]
    dsimp [bound]
    omega
  · apply Eval.seq (copy_eval 0 5 d (by decide) (by decide) (by decide) h8)
    apply Eval.seq hb
    apply Eval.seq (.base (.atom _ _))
    apply Eval.seq (copy_eval 0 1 c (by decide) (by decide) (by decide) hc8)
    apply Eval.seq he
    exact Eval.seq (clear_eval 1 q) (Eval.seq (.base (.atom _ _)) (.base (.atom _ _)))
  · simpa [finished, cleared, StackRoutines.clearStacks,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using hqinv.1
  · simpa [finished, cleared, StackRoutines.clearStacks,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using hqinv.2.1
  · simpa [finished, cleared, StackRoutines.clearStacks,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using hqinv.2.2.1
  · rcases hqinv with ⟨_, _, _, hq5, hq6, hq7, hq8, _⟩
    simp [workEmpty, finished, StackRoutines.clearStacks,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr,
      hq2, hq5, hq6, hq7, hq8]
  · simp [finished, readRegs, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, hq10, hq11, passes, Bool.and_comm]

theorem passes_iff (width size : List Bool) (G : Family) :
    passes width size G = true ↔ G.length = BinaryArithmetic.toNat size ∧ ∀ C ∈ G, C.length = BinaryArithmetic.toNat width := by
  simp [passes, List.any_eq_false]

theorem guard_correct (width size : List Bool) (G : Family) (d : Data)
    (h0 : d.stacks 0 = familyCode G) (h3 : d.stacks 3 = width) (h4 : d.stacks 4 = size)
    (hw : workEmpty d) :
    ∃ e : Data, RunsIn program (bound width size G)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks 0 = familyCode G ∧ e.stacks 3 = width ∧ e.stacks 4 = size ∧ workEmpty e ∧
      (e.regs 10 = true ↔ G.length = BinaryArithmetic.toNat size ∧ ∀ C ∈ G, C.length = BinaryArithmetic.toNat width) := by
  obtain ⟨n, hn, e, he, h0, h3, h4, hw, hg⟩ := command_eval width size G d h0 h3 h4 hw
  refine ⟨e, ⟨n + 1, hn, compiled_halt_trace he 0 0⟩, h0, h3, h4, hw, ?_⟩
  rw [hg, passes_iff]

theorem primitive_execution (width size : List Bool) (G : Family) (d : Data)
    (h0 : d.stacks 0 = familyCode G) (h3 : d.stacks 3 = width) (h4 : d.stacks 4 = size)
    (hw : workEmpty d) :
    ∃ e : Data, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * bound width size G)
      (primitiveCfg program (d.withPC (some program.entry)))
      (primitiveCfg program (e.withPC none)) ∧
      e.stacks 0 = familyCode G ∧ e.stacks 3 = width ∧ e.stacks 4 = size ∧ workEmpty e ∧
      (e.regs 10 = true ↔ G.length = BinaryArithmetic.toNat size ∧ ∀ C ∈ G, C.length = BinaryArithmetic.toNat width) := by
  obtain ⟨e, he, h0, h3, h4, hw, hg⟩ := guard_correct width size G d h0 h3 h4 hw
  exact ⟨e, BitProgram.primitive_execution program he, h0, h3, h4, hw, hg⟩

end SubexponentialSAT.FamilySizeGuardProgram

end OAI.Algorithms
