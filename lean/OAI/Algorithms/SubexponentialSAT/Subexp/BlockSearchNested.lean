import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCoefficientFrames

namespace OAI.Algorithms

/-! Actual composition of the coefficient, split, and table scans. -/

namespace SubexponentialSAT.Subexp.BlockSearchNested

open BitProgram StructuredCalls BlockSearchProgram BlockSearchLoop

abbrev Data := StructuredProgram.State 24 42

def clearState (a : Data) (src : Fin 42) : Data :=
  ⟨readRegs a.regs 21 22 none, StackRoutines.clearStacks src a.stacks⟩

theorem clear_eval (a : Data) (src : Fin 42) :
    Eval (clear src) (2 * (a.stacks src).length + 3) a (clearState a src) :=
  TupleProgram.clear_eval src 21 22 a

def finishDimension (a : Data) : Data :=
  (StructuredProgram.Atom.set (12 : Fin 24) true).eval
    ((StructuredProgram.Atom.set (11 : Fin 24) false).eval
      ((StructuredProgram.Atom.copy (13 : Fin 24) 16).eval a))

def coefficientScanCost (cost : List Bool → ℕ) (records : List (List Bool)) : ℕ :=
  9 * (ProgramEncoding.encodeRecords records).length +
    RecordPrograms.budget (fun bits => cost bits + 2) records + 14

def dimensionCost (oldLength : ℕ) (cost : List Bool → ℕ)
    (records : List (List Bool)) (split : List Bool) : ℕ :=
  2 * oldLength + 9 * split.length + coefficientScanCost cost records + 14

/-- One split callback installs its split, runs the actual complete scalar
scan, and restores the enclosing iterator's physical boundary. -/
theorem dimensionCallback_eval (matrixPair : Cmd 24 42) (ctx : Context)
    (table split : List Bool) (test : List Bool → Bool) (cost : List Bool → ℕ)
    (valid : List Bool → Prop)
    (contract : CoefficientContract matrixPair ctx table split test cost valid)
    (records : List (List Bool)) (base : Data)
    (hv : ∀ bits ∈ records, valid bits)
    (hb : CoefficientEntry ctx table (base.stacks 8) base)
    (h4 : base.stacks 4 = split)
    (hs : base.stacks 14 = ProgramEncoding.encodeRecords records)
    (h6 : base.stacks 6 = []) (h7 : base.stacks 7 = []) :
    ∃ n next,
      n ≤ dimensionCost (base.stacks 8).length cost records split ∧
      next.stacks = Function.update (Function.update base.stacks 8 split) 4 [] ∧
      (∀ j : Fin 24, 8 ≤ j.val → j.val ≤ 10 → next.regs j = base.regs j) ∧
      next.regs 11 = false ∧ next.regs 12 = true ∧ next.regs 13 = records.all test ∧
      Eval (dimensionCallback matrixPair) n base next := by
  let a1 := clearState base 8
  let a2 := BlockCoefficientFrames.copyState a1 4 8
  have e1 := clear_eval base 8
  have h9 : base.stacks 9 = [] := hb.2.2.2.2.2.2.2.1
  have e2 := BlockCoefficientFrames.copy_eval a1 4 8 (by decide) (by decide)
    (by decide) (by simpa [a1, clearState, StackRoutines.clearStacks] using h9)
  have a2st : a2.stacks = Function.update base.stacks 8 split := by
    funext j
    by_cases h : j = 8
    · subst j; simp [a2, a1, BlockCoefficientFrames.copyState, clearState,
        StackRoutines.copyStacks, StackRoutines.clearStacks, h4]
    · simp [a2, a1, BlockCoefficientFrames.copyState, clearState,
        StackRoutines.copyStacks, StackRoutines.clearStacks, h]
  have ha2 : CoefficientEntry ctx table split a2 := by
    rcases hb with ⟨hm, hz, hM, hr, hd, ht, _, hw⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [a2st] using hm
    · simpa [a2st] using hz
    · simpa [a2st] using hM
    · simpa [a2st] using hr
    · simpa [a2st] using hd
    · simpa [a2st] using ht
    · simp [a2st]
    · refine ⟨?_, ?_⟩
      · simpa [a2st] using hw.1
      · intro j hj h27 h36 h38 h39 h41
        have h8 : j ≠ 8 := by intro h; subst j; change 22 ≤ 8 at hj; omega
        simpa [a2st, h8] using hw.2 j hj h27 h36 h38 h39 h41
  obtain ⟨n, a3, hn, hst, hreg, hresult, e3⟩ := coefficientScan_eval matrixPair ctx
    table split test cost valid contract records a2 hv ha2
    (by simpa [a2st] using hs) (by simpa [a2st] using h6) (by simpa [a2st] using h7)
  let a4 := clearState a3 4
  let next := finishDimension a4
  have e4 := clear_eval a3 4
  have e5 : Eval (sequence [atom (.copy 13 16), atom (.set 11 false), atom (.set 12 true)])
      (1 + (1 + (1 + 0))) a4 next :=
    (Eval.base (.atom _ _)).seq ((Eval.base (.atom _ _)).seq
      ((Eval.base (.atom _ _)).seq (Eval.base (.skip _))))
  have hlen1 : (a1.stacks 4).length = split.length := by
    simp [a1, clearState, StackRoutines.clearStacks, h4]
  have hlen3 : (a3.stacks 4).length = split.length := by simp [hst, a2st, h4]
  refine ⟨_, next, ?_, ?_, ?_, ?_, ?_, ?_, e1.seq (e2.seq (e3.seq (e4.seq e5)))⟩
  · rw [hlen1, hlen3]
    change n ≤ coefficientScanCost cost records at hn
    unfold dimensionCost
    omega
  · change next.stacks = _
    simp [next, finishDimension, a4, clearState, StackRoutines.clearStacks,
      hst, a2st, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]
  · intro j hj hk
    have h11 : j ≠ 11 := by intro h; subst j; change 11 ≤ 10 at hk; omega
    have h12 : j ≠ 12 := by intro h; subst j; change 12 ≤ 10 at hk; omega
    have h13 : j ≠ 13 := by intro h; subst j; change 13 ≤ 10 at hk; omega
    have h21 : j ≠ 21 := by intro h; subst j; change 21 ≤ 10 at hk; omega
    have h22 : j ≠ 22 := by intro h; subst j; change 22 ≤ 10 at hk; omega
    have hr3 := hreg j hj (by omega)
    simpa [next, finishDimension, a4, clearState, a2, a1,
      BlockCoefficientFrames.copyState, readRegs,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr,
      h11, h12, h13, h21, h22] using hr3
  · simp [next, finishDimension, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]
  · simp [next, finishDimension, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]
  · simpa [next, finishDimension, a4, clearState, readRegs,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using hresult

def DimensionEntry (ctx : Context) (table : List Bool) (records : List (List Bool))
    (limit : ℕ) (a : Data) : Prop :=
  CoefficientEntry ctx table (a.stacks 8) a ∧
  a.stacks 14 = ProgramEncoding.encodeRecords records ∧
  a.stacks 6 = [] ∧ a.stacks 7 = [] ∧ (a.stacks 8).length ≤ limit

theorem coefficientEntry_dimension_state (ctx : Context) (table split : List Bool)
    (base : Data) (v pr f : Bool) (src out : List Bool)
    (hb : CoefficientEntry ctx table split base) :
    CoefficientEntry ctx table split
      (RecordPrograms.state dimensionPorts.toPorts base v pr f src out) := by
  rcases hb with ⟨hm, hz, hM, hr, hd, ht, hs, hw⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [RecordPrograms.state, dimensionPorts] using hm
  · simpa [RecordPrograms.state, dimensionPorts] using hz
  · simpa [RecordPrograms.state, dimensionPorts] using hM
  · simpa [RecordPrograms.state, dimensionPorts] using hr
  · simpa [RecordPrograms.state, dimensionPorts] using hd
  · simpa [RecordPrograms.state, dimensionPorts] using ht
  · simpa [RecordPrograms.state, dimensionPorts] using hs
  · refine ⟨?_, ?_⟩
    · simpa [RecordPrograms.state, dimensionPorts] using hw.1
    · intro j hj h27 h36 h38 h39 h41
      have h3 : j ≠ 3 := by intro h; subst j; change 22 ≤ 3 at hj; omega
      have h4 : j ≠ 4 := by intro h; subst j; change 22 ≤ 4 at hj; omega
      simpa [RecordPrograms.state, dimensionPorts, h3, h4] using
        hw.2 j hj h27 h36 h38 h39 h41

/-- A split record is executable unary data. Its length supplies the bound;
the predicate family is implemented by the supplied coefficient contract. -/
theorem dimensionContract (matrixPair : Cmd 24 42) (ctx : Context)
    (table : List Bool) (records : List (List Bool)) (limit : ℕ)
    (test : List Bool → List Bool → Bool) (cost : List Bool → List Bool → ℕ)
    (validSplit : List Bool → Prop) (validCoefficient : List Bool → Prop)
    (hreversal : ∀ bits, validSplit bits → bits.reverse = bits)
    (hlimit : ∀ bits, validSplit bits → bits.length ≤ limit)
    (hrecords : ∀ bits ∈ records, validCoefficient bits)
    (contract : ∀ split, validSplit split →
      CoefficientContract matrixPair ctx table split (test split) (cost split) validCoefficient) :
    RecordPrograms.CallbackContractWithOn dimensionPorts.toPorts
      (dimensionCallback matrixPair) (fun split => records.all (test split))
      (fun split => dimensionCost limit (cost split) records split)
      (DimensionEntry ctx table records limit)
      (fun split a b => b.stacks = Function.update a.stacks 8 split ∧
        ∀ j : Fin 24, 8 ≤ j.val → j.val ≤ 10 → b.regs j = a.regs j) validSplit := by
  intro split tail base hsplit hb
  let start := RecordPrograms.state dimensionPorts.toPorts base false true false tail split.reverse
  have he : CoefficientEntry ctx table (start.stacks 8) start := by
    simpa [start, RecordPrograms.state, dimensionPorts] using
      coefficientEntry_dimension_state ctx table (base.stacks 8) base false true false
        tail split.reverse hb.1
  obtain ⟨n, out, hn, hst, hreg, h11, h12, h13, run⟩ :=
    dimensionCallback_eval matrixPair ctx table split (test split) (cost split)
      validCoefficient (contract split hsplit) records start hrecords he
      (by simp [start, RecordPrograms.state, dimensionPorts, hreversal split hsplit])
      (by simpa [start, RecordPrograms.state, dimensionPorts] using hb.2.1)
      (by simpa [start, RecordPrograms.state, dimensionPorts] using hb.2.2.1)
      (by simpa [start, RecordPrograms.state, dimensionPorts] using hb.2.2.2.1)
  let next : Data := ⟨out.regs, Function.update base.stacks 8 split⟩
  have hnext : DimensionEntry ctx table records limit next := by
    rcases hb.1 with ⟨hm, hz, hM, hr, hd, ht, _, hw⟩
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩, ?_, ?_, ?_, ?_⟩
    · simpa [next] using hm
    · simpa [next] using hz
    · simpa [next] using hM
    · simpa [next] using hr
    · simpa [next] using hd
    · simpa [next] using ht
    · refine ⟨?_, ?_⟩
      · simpa [next] using hw.1
      · intro j hj h27 h36 h38 h39 h41
        have h8 : j ≠ 8 := by intro h; subst j; change 22 ≤ 8 at hj; omega
        simpa [next, h8] using hw.2 j hj h27 h36 h38 h39 h41
    · simpa [next] using hb.2.1
    · simpa [next] using hb.2.2.1
    · simpa [next] using hb.2.2.2.1
    · simpa [next] using hlimit split hsplit
  have hstate : RecordPrograms.state dimensionPorts.toPorts next false true
      (records.all (test split)) tail [] = out := by
    have hregs : (RecordPrograms.state dimensionPorts.toPorts next false true
        (records.all (test split)) tail []).regs = out.regs := by
      funext j
      by_cases hj11 : j = 11
      · subst j; simpa [RecordPrograms.state, dimensionPorts] using h11.symm
      by_cases hj12 : j = 12
      · subst j; simpa [RecordPrograms.state, dimensionPorts] using h12.symm
      by_cases hj13 : j = 13
      · subst j; simpa [RecordPrograms.state, dimensionPorts] using h13.symm
      simp [RecordPrograms.state, dimensionPorts, next, hj11, hj12, hj13]
    have hstacks : (RecordPrograms.state dimensionPorts.toPorts next false true
        (records.all (test split)) tail []).stacks = out.stacks := by
      rw [hst]
      funext j
      by_cases hj3 : j = 3 <;> by_cases hj4 : j = 4 <;> by_cases hj8 : j = 8 <;>
        subst_vars <;> simp_all [RecordPrograms.state, dimensionPorts, next, start]
    cases out
    exact congrArg₂ StructuredProgram.State.mk hregs hstacks
  refine ⟨n, next, ?_, hnext, ⟨rfl, ?_⟩, ?_⟩
  · have hold : (start.stacks 8).length ≤ limit := by
      simpa [start, RecordPrograms.state, dimensionPorts] using hb.2.2.2.2
    change n ≤ dimensionCost limit (cost split) records split
    unfold dimensionCost at hn ⊢
    omega
  · intro j hj hk
    have h11 : j ≠ 11 := by intro h; subst j; change 11 ≤ 10 at hk; omega
    have h12 : j ≠ 12 := by intro h; subst j; change 12 ≤ 10 at hk; omega
    have h13 : j ≠ 13 := by intro h; subst j; change 13 ≤ 10 at hk; omega
    simpa [next, start, RecordPrograms.state, dimensionPorts, h11, h12, h13] using hreg j hj hk
  · simpa only [hstate] using run

def dimensionScanCost (limit : ℕ) (cost : List Bool → List Bool → ℕ)
    (coefficients dimensions : List (List Bool)) : ℕ :=
  9 * (ProgramEncoding.encodeRecords dimensions).length +
    RecordPrograms.budget (fun split => dimensionCost limit (cost split) coefficients split)
      dimensions + 12

/-- The actual saved split scan retains a successful split, while framing
the table iterator and every stack except the selected split. -/
theorem dimensionScan_eval (matrixPair : Cmd 24 42) (ctx : Context)
    (table : List Bool) (coefficients dimensions : List (List Bool)) (limit : ℕ)
    (test : List Bool → List Bool → Bool) (cost : List Bool → List Bool → ℕ)
    (validSplit : List Bool → Prop) (validCoefficient : List Bool → Prop)
    (hreversal : ∀ bits, validSplit bits → bits.reverse = bits)
    (hlimit : ∀ bits, validSplit bits → bits.length ≤ limit)
    (hcoefficients : ∀ bits ∈ coefficients, validCoefficient bits)
    (hdimensions : ∀ bits ∈ dimensions, validSplit bits)
    (contract : ∀ split, validSplit split →
      CoefficientContract matrixPair ctx table split (test split) (cost split) validCoefficient)
    (base : Data) (hb : DimensionEntry ctx table coefficients limit base)
    (hs : base.stacks 12 = ProgramEncoding.encodeRecords dimensions)
    (h3 : base.stacks 3 = []) (h4 : base.stacks 4 = []) :
    ∃ n next,
      n ≤ dimensionScanCost limit cost coefficients dimensions ∧
      DimensionEntry ctx table coefficients limit next ∧
      (∀ j : Fin 42, j ≠ 8 → next.stacks j = base.stacks j) ∧
      (∀ j : Fin 24, 8 ≤ j.val → j.val ≤ 10 → next.regs j = base.regs j) ∧
      next.regs 13 = dimensions.any (fun split => coefficients.all (test split)) ∧
      (dimensions.any (fun split => coefficients.all (test split)) = true →
        ∃ split ∈ dimensions, coefficients.all (test split) = true ∧ next.stacks 8 = split) ∧
      Eval (savedAnyCommand dimensionPorts (dimensionCallback matrixPair)) n base next := by
  let pred := fun split => coefficients.all (test split)
  let inv := fun a : Data => DimensionEntry ctx table coefficients limit a ∧
    (∀ j : Fin 42, j ≠ 8 → a.stacks j = base.stacks j) ∧
    ∀ j : Fin 24, 8 ≤ j.val → j.val ≤ 10 → a.regs j = base.regs j
  have hc : RecordPrograms.CallbackContractWithOn dimensionPorts.toPorts
      (dimensionCallback matrixPair) pred
      (fun split => dimensionCost limit (cost split) coefficients split) inv
      (fun split _ b => b.stacks 8 = split) validSplit := by
    intro split tail a hv ha
    obtain ⟨n, b, hn, hi, heffect, heval⟩ := dimensionContract matrixPair ctx table coefficients
      limit test cost validSplit validCoefficient hreversal hlimit hcoefficients contract
      split tail a hv ha.1
    refine ⟨n, b, hn, ⟨hi, ?_, ?_⟩, ?_, heval⟩
    · intro j hj
      rw [heffect.1, Function.update_of_ne hj]
      exact ha.2.1 j hj
    · intro j hj hk
      exact (heffect.2 j hj hk).trans (ha.2.2 j hj hk)
    · simp [heffect.1]
  have h9 : base.stacks dimensionPorts.temporary = [] := hb.1.2.2.2.2.2.2.2.1
  obtain ⟨n, b, hn, hi, history, he⟩ := savedAnyCommand_eval_with dimensionPorts
    (dimensionCallback matrixPair) pred
    (fun split => dimensionCost limit (cost split) coefficients split) inv
    (fun split _ b => b.stacks 8 = split) validSplit hc dimensions base hdimensions
    ⟨hb, fun _ _ => rfl, fun _ _ _ => rfl⟩ hs h9
    (base.regs 11) (base.regs 12) (base.regs 13)
  let next := RecordPrograms.state dimensionPorts.toPorts b false true
    (dimensions.any pred) [] []
  have hstart : RecordPrograms.state dimensionPorts.toPorts base (base.regs 11)
      (base.regs 12) (base.regs 13) [] [] = base := by
    apply RecordPrograms.state_eq_self <;> simp [dimensionPorts, h3, h4]
  have hst8 : next.stacks 8 = b.stacks 8 := by
    simp [next, RecordPrograms.state, dimensionPorts]
  have hentry : DimensionEntry ctx table coefficients limit next := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hst8] using coefficientEntry_dimension_state ctx table (b.stacks 8) b
        false true (dimensions.any pred) [] [] hi.1.1
    · simpa [next, RecordPrograms.state, dimensionPorts] using hi.1.2.1
    · simpa [next, RecordPrograms.state, dimensionPorts] using hi.1.2.2.1
    · simpa [next, RecordPrograms.state, dimensionPorts] using hi.1.2.2.2.1
    · simpa only [hst8] using hi.1.2.2.2.2
  refine ⟨n, next, hn, hentry, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hjs : j = 3
    · subst j; simp [next, RecordPrograms.state, dimensionPorts, h3]
    by_cases hjp : j = 4
    · subst j; simp [next, RecordPrograms.state, dimensionPorts, h4]
    simpa [next, RecordPrograms.state, dimensionPorts, hjs, hjp] using hi.2.1 j hj
  · intro j hj hk
    have h11 : j ≠ 11 := by intro h; subst j; change 11 ≤ 10 at hk; omega
    have h12 : j ≠ 12 := by intro h; subst j; change 12 ≤ 10 at hk; omega
    have h13 : j ≠ 13 := by intro h; subst j; change 13 ≤ 10 at hk; omega
    simpa [next, RecordPrograms.state, dimensionPorts, h11, h12, h13] using hi.2.2 j hj hk
  · exact RecordPrograms.state_found dimensionPorts.toPorts b false true
      (dimensions.any pred) [] []
  · intro success
    obtain ⟨split, hmem, ht, hout⟩ := selected_of_visits 8 pred history success
    exact ⟨split, hmem, ht, hst8.trans hout⟩
  · simpa only [hstart] using he

end SubexponentialSAT.Subexp.BlockSearchNested

end OAI.Algorithms
