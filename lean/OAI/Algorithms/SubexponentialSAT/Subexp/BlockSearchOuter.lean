import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchNested

namespace OAI.Algorithms

/-! Actual table enumeration around the checked split and coefficient scans. -/

namespace SubexponentialSAT.Subexp.BlockSearchOuter

open BitProgram StructuredCalls BlockSearchProgram BlockSearchLoop BlockSearchNested

abbrev Data := StructuredProgram.State 24 42

def transferState (a : Data) (src dst : Fin 42) : Data :=
  ⟨readRegs a.regs 21 22 none, StackRoutines.transferStacks src dst a.stacks⟩

theorem transfer_eval (a : Data) (src dst : Fin 42) (h : src ≠ dst) :
    Eval (transfer src dst) (3 * (a.stacks src).length + 3) a (transferState a src dst) :=
  TupleProgram.transfer_eval src dst 21 22 h (by decide) a

def finishTable (a : Data) : Data :=
  (StructuredProgram.Atom.set (9 : Fin 24) true).eval
    ((StructuredProgram.Atom.set (8 : Fin 24) false).eval
      ((StructuredProgram.Atom.copy (10 : Fin 24) 13).eval a))

def TableEntry (ctx : Context) (coefficients dimensions : List (List Bool))
    (splitLimit tableLimit : ℕ) (a : Data) : Prop :=
  DimensionEntry ctx (a.stacks 41) coefficients splitLimit a ∧
  a.stacks 12 = ProgramEncoding.encodeRecords dimensions ∧
  a.stacks 3 = [] ∧ a.stacks 4 = [] ∧ (a.stacks 41).length ≤ tableLimit

def tableCost (oldLength splitLimit : ℕ) (cost : List Bool → List Bool → ℕ)
    (coefficients dimensions : List (List Bool)) (table : List Bool) : ℕ :=
  2 * oldLength + 3 * table.length +
    dimensionScanCost splitLimit cost coefficients dimensions + 9

theorem dimensionEntry_of_stacks_eq (ctx : Context) (table : List Bool)
    (coefficients : List (List Bool)) (limit : ℕ) {a b : Data}
    (hs : b.stacks = a.stacks) (h : DimensionEntry ctx table coefficients limit a) :
    DimensionEntry ctx table coefficients limit b := by
  simpa only [DimensionEntry, CoefficientEntry, WorkReady, hs] using h

/-- One concrete table callback installs a table in forward scalar order and
retains the split selected by the actual inner search. -/
theorem tableCallback_eval (matrixPair : Cmd 24 42) (ctx : Context)
    (table : List Bool) (coefficients dimensions : List (List Bool)) (limit tableLimit : ℕ)
    (test : List Bool → List Bool → Bool) (cost : List Bool → List Bool → ℕ)
    (validSplit : List Bool → Prop) (validCoefficient : List Bool → Prop)
    (hreversal : ∀ bits, validSplit bits → bits.reverse = bits)
    (hlimit : ∀ bits, validSplit bits → bits.length ≤ limit)
    (hcoefficients : ∀ bits ∈ coefficients, validCoefficient bits)
    (hdimensions : ∀ bits ∈ dimensions, validSplit bits)
    (contract : ∀ split, validSplit split →
      CoefficientContract matrixPair ctx table split (test split) (cost split) validCoefficient)
    (base : Data) (hb : TableEntry ctx coefficients dimensions limit tableLimit base)
    (h2 : base.stacks 2 = table.reverse) :
    ∃ n next,
      n ≤ tableCost (base.stacks 41).length limit cost coefficients dimensions table ∧
      DimensionEntry ctx table coefficients limit next ∧
      (∀ j : Fin 42, j ≠ 8 → j ≠ 41 → j ≠ 2 → next.stacks j = base.stacks j) ∧
      next.stacks 41 = table ∧ next.stacks 2 = [] ∧
      next.regs 8 = false ∧ next.regs 9 = true ∧
      next.regs 10 = dimensions.any (fun split => coefficients.all (test split)) ∧
      (dimensions.any (fun split => coefficients.all (test split)) = true →
        ∃ split ∈ dimensions, coefficients.all (test split) = true ∧ next.stacks 8 = split) ∧
      Eval (tableCallback matrixPair) n base next := by
  let a1 := clearState base 41
  let a2 := transferState a1 2 41
  have e1 := clear_eval base 41
  have e2 := transfer_eval a1 2 41 (by decide)
  have a2st : a2.stacks = Function.update (Function.update base.stacks 2 []) 41 table := by
    funext j
    by_cases hj2 : j = 2 <;> by_cases hj41 : j = 41 <;> subst_vars <;>
      simp_all [a2, a1, transferState, clearState, StackRoutines.transferStacks,
        StackRoutines.clearStacks]
  have ha2 : DimensionEntry ctx table coefficients limit a2 := by
    rcases hb.1.1 with ⟨hm, hz, hM, hr, hd, ht, hsplit, hw⟩
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩, ?_, ?_, ?_, ?_⟩
    · simpa [a2st] using hm
    · simpa [a2st] using hz
    · simpa [a2st] using hM
    · simpa [a2st] using hr
    · simpa [a2st] using hd
    · simp [a2st]
    · refine ⟨?_, ?_⟩
      · simpa [a2st] using hw.1
      · intro j hj h27 h36 h38 h39 h41
        have h2 : j ≠ 2 := by intro h; subst j; change 22 ≤ 2 at hj; omega
        simpa [a2st, h2, h41] using hw.2 j hj h27 h36 h38 h39 h41
    · simpa [a2st] using hb.1.2.1
    · simpa [a2st] using hb.1.2.2.1
    · simpa [a2st] using hb.1.2.2.2.1
    · simpa [a2st] using hb.1.2.2.2.2
  obtain ⟨n, a3, hn, hi, hframe, hreg, hresult, hselected, e3⟩ :=
    dimensionScan_eval matrixPair ctx table coefficients dimensions limit test cost
      validSplit validCoefficient hreversal hlimit hcoefficients hdimensions contract a2 ha2
      (by simpa [a2st] using hb.2.1) (by simpa [a2st] using hb.2.2.1)
      (by simpa [a2st] using hb.2.2.2.1)
  let next := finishTable a3
  have e4 : Eval (sequence [atom (.copy 10 13), atom (.set 8 false), atom (.set 9 true)])
      (1 + (1 + (1 + 0))) a3 next :=
    (Eval.base (.atom _ _)).seq ((Eval.base (.atom _ _)).seq
      ((Eval.base (.atom _ _)).seq (Eval.base (.skip _))))
  have nextst : next.stacks = a3.stacks := rfl
  refine ⟨_, next, ?_, dimensionEntry_of_stacks_eq _ _ _ _ nextst hi,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, e1.seq (e2.seq (e3.seq e4))⟩
  · have hl : (a1.stacks 2).length = table.length := by
      simp [a1, clearState, StackRoutines.clearStacks, h2]
    change (2 * (base.stacks 41).length + 3) +
      ((3 * (a1.stacks 2).length + 3) + (n + (1 + (1 + (1 + 0))))) ≤ _
    rw [hl]
    unfold tableCost
    omega
  · intro j h8 h41 h2
    rw [nextst, hframe j h8, a2st]
    simp [h41, h2]
  · rw [nextst, hframe 41 (by decide), a2st]
    simp
  · rw [nextst, hframe 2 (by decide), a2st]
    simp
  · simp [next, finishTable, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]
  · simp [next, finishTable, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]
  · simpa [next, finishTable, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using hresult
  · simpa only [nextst] using hselected

theorem tableEntry_state (ctx : Context) (coefficients dimensions : List (List Bool))
    (limit tableLimit : ℕ) (base : Data) (v pr f : Bool) (src payload : List Bool)
    (hb : TableEntry ctx coefficients dimensions limit tableLimit base) :
    TableEntry ctx coefficients dimensions limit tableLimit
      (RecordPrograms.state tablePorts base v pr f src payload) := by
  rcases hb.1.1 with ⟨hm, hz, hM, hr, hd, ht, hsplit, hw⟩
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simpa [RecordPrograms.state, tablePorts] using hm
  · simpa [RecordPrograms.state, tablePorts] using hz
  · simpa [RecordPrograms.state, tablePorts] using hM
  · simpa [RecordPrograms.state, tablePorts] using hr
  · simpa [RecordPrograms.state, tablePorts] using hd
  · refine ⟨?_, ?_⟩
    · simpa [RecordPrograms.state, tablePorts] using hw.1
    · intro j hj h27 h36 h38 h39 h41
      have h0 : j ≠ 0 := by intro h; subst j; change 22 ≤ 0 at hj; omega
      have h2 : j ≠ 2 := by intro h; subst j; change 22 ≤ 2 at hj; omega
      simpa [RecordPrograms.state, tablePorts, h0, h2] using hw.2 j hj h27 h36 h38 h39 h41
  · simpa [RecordPrograms.state, tablePorts] using hb.1.2.1
  · simpa [RecordPrograms.state, tablePorts] using hb.1.2.2.1
  · simpa [RecordPrograms.state, tablePorts] using hb.1.2.2.2.1
  · simpa [RecordPrograms.state, tablePorts] using hb.1.2.2.2.2
  · simpa [RecordPrograms.state, tablePorts] using hb.2.1
  · simpa [RecordPrograms.state, tablePorts] using hb.2.2.1
  · simpa [RecordPrograms.state, tablePorts] using hb.2.2.2.1
  · simpa [RecordPrograms.state, tablePorts] using hb.2.2.2.2

def tableTest (coefficients dimensions : List (List Bool))
    (test : List Bool → List Bool → List Bool → Bool) (table : List Bool) : Bool :=
  dimensions.any (fun split => coefficients.all (test table split))

def Selected (coefficients dimensions : List (List Bool))
    (test : List Bool → List Bool → List Bool → Bool) (table : List Bool) (a : Data) : Prop :=
  a.stacks 41 = table ∧
  (tableTest coefficients dimensions test table = true →
    ∃ split ∈ dimensions, coefficients.all (test table split) = true ∧ a.stacks 8 = split)

/-- The only lower-level premise is a measured execution of the concrete
coefficient callback; table/split control is proved here from fixed code. -/
theorem tableContract (matrixPair : Cmd 24 42) (ctx : Context)
    (coefficients dimensions : List (List Bool)) (limit tableLimit : ℕ)
    (test : List Bool → List Bool → List Bool → Bool)
    (cost : List Bool → List Bool → List Bool → ℕ)
    (validTable validSplit validCoefficient : List Bool → Prop)
    (htableLimit : ∀ bits, validTable bits → bits.length ≤ tableLimit)
    (hreversal : ∀ bits, validSplit bits → bits.reverse = bits)
    (hlimit : ∀ bits, validSplit bits → bits.length ≤ limit)
    (hcoefficients : ∀ bits ∈ coefficients, validCoefficient bits)
    (hdimensions : ∀ bits ∈ dimensions, validSplit bits)
    (contract : ∀ table, validTable table → ∀ split, validSplit split →
      CoefficientContract matrixPair ctx table split (test table split) (cost table split)
        validCoefficient) :
    RecordPrograms.CallbackContractWithOn tablePorts (tableCallback matrixPair)
      (tableTest coefficients dimensions test)
      (fun table => tableCost tableLimit limit (cost table) coefficients dimensions table)
      (TableEntry ctx coefficients dimensions limit tableLimit)
      (fun table _ b => Selected coefficients dimensions test table b) validTable := by
  intro table tail base htable hb
  let start := RecordPrograms.state tablePorts base false true false tail table.reverse
  have hstart := tableEntry_state ctx coefficients dimensions limit tableLimit base
    false true false tail table.reverse hb
  obtain ⟨n, out, hn, hi, hframe, h41, h2, h8, h9, h10, hselected, heval⟩ :=
    tableCallback_eval matrixPair ctx table coefficients dimensions limit tableLimit
      (test table) (cost table) validSplit validCoefficient hreversal hlimit hcoefficients
      hdimensions (contract table htable) start hstart
      (by simp [start, RecordPrograms.state, tablePorts])
  have hout : TableEntry ctx coefficients dimensions limit tableLimit out := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [h41] using hi
    · rw [hframe 12 (by decide) (by decide) (by decide)]
      simpa [start, RecordPrograms.state, tablePorts] using hb.2.1
    · rw [hframe 3 (by decide) (by decide) (by decide)]
      simpa [start, RecordPrograms.state, tablePorts] using hb.2.2.1
    · rw [hframe 4 (by decide) (by decide) (by decide)]
      simpa [start, RecordPrograms.state, tablePorts] using hb.2.2.2.1
    · simpa only [h41] using htableLimit table htable
  let next := RecordPrograms.state tablePorts out false true
    (tableTest coefficients dimensions test table) (base.stacks 0) (base.stacks 2)
  have hnext := tableEntry_state ctx coefficients dimensions limit tableLimit out false true
    (tableTest coefficients dimensions test table) (base.stacks 0) (base.stacks 2) hout
  have h0 : out.stacks 0 = tail := by
    rw [hframe 0 (by decide) (by decide) (by decide)]
    simp [start, RecordPrograms.state, tablePorts]
  have hstate : RecordPrograms.state tablePorts next false true
      (tableTest coefficients dimensions test table) tail [] = out := by
    rw [RecordPrograms.state_state]
    exact RecordPrograms.state_eq_self tablePorts out false true
      (tableTest coefficients dimensions test table) tail [] h8 h9 h10 h0 h2
  refine ⟨n, next, ?_, hnext, ⟨?_, ?_⟩, ?_⟩
  · have hold : (start.stacks 41).length ≤ tableLimit := by
      simpa [start, RecordPrograms.state, tablePorts] using hb.2.2.2.2
    change n ≤ tableCost tableLimit limit (cost table) coefficients dimensions table
    unfold tableCost at hn ⊢
    omega
  · simpa [next, RecordPrograms.state, tablePorts] using h41
  · intro success
    obtain ⟨split, hmem, ht, hs⟩ := hselected success
    exact ⟨split, hmem, ht, by simpa [next, RecordPrograms.state, tablePorts] using hs⟩
  · simpa only [hstate] using heval

theorem selected_of_history (coefficients dimensions tables : List (List Bool))
    (test : List Bool → List Bool → List Bool → Bool) {base next : Data}
    (history : RecordPrograms.Visits (tableTest coefficients dimensions test)
      (fun table _ b => Selected coefficients dimensions test table b) tables base next)
    (success : tables.any (tableTest coefficients dimensions test) = true) :
    ∃ table ∈ tables, ∃ split ∈ dimensions,
      coefficients.all (test table split) = true ∧
      next.stacks 41 = table ∧ next.stacks 8 = split := by
  induction history with
  | nil => simp at success
  | @hit table rest base next ht he =>
      obtain ⟨split, hmem, htest, hsplit⟩ := he.2 ht
      exact ⟨table, by simp, split, hmem, htest, he.1, hsplit⟩
  | @miss table rest base middle next ht he history ih =>
      have hr : rest.any (tableTest coefficients dimensions test) = true := by
        simpa [ht] using success
      obtain ⟨table', hmem, split, hsplit, htest, htable', hsplit'⟩ := ih hr
      exact ⟨table', by simp [hmem], split, hsplit, htest, htable', hsplit'⟩

def searchCost (limit tableLimit : ℕ)
    (cost : List Bool → List Bool → List Bool → ℕ)
    (coefficients dimensions tables : List (List Bool)) : ℕ :=
  RecordPrograms.budget (fun table =>
    tableCost tableLimit limit (cost table) coefficients dimensions table) tables +
    2 * (ProgramEncoding.encodeRecords tables).length + 6

theorem command_eval (matrixPair : Cmd 24 42) (ctx : Context)
    (coefficients dimensions tables : List (List Bool)) (limit tableLimit : ℕ)
    (test : List Bool → List Bool → List Bool → Bool)
    (cost : List Bool → List Bool → List Bool → ℕ)
    (validTable validSplit validCoefficient : List Bool → Prop)
    (htableLimit : ∀ bits, validTable bits → bits.length ≤ tableLimit)
    (hreversal : ∀ bits, validSplit bits → bits.reverse = bits)
    (hlimit : ∀ bits, validSplit bits → bits.length ≤ limit)
    (hcoefficients : ∀ bits ∈ coefficients, validCoefficient bits)
    (hdimensions : ∀ bits ∈ dimensions, validSplit bits)
    (htables : ∀ bits ∈ tables, validTable bits)
    (contract : ∀ table, validTable table → ∀ split, validSplit split →
      CoefficientContract matrixPair ctx table split (test table split) (cost table split)
        validCoefficient)
    (success : tables.any (tableTest coefficients dimensions test) = true)
    (base : Data) (hb : TableEntry ctx coefficients dimensions limit tableLimit base)
    (h0 : base.stacks 0 = ProgramEncoding.encodeRecords tables) (h2 : base.stacks 2 = []) :
    ∃ n next, n ≤ searchCost limit tableLimit cost coefficients dimensions tables ∧
      (∃ table ∈ tables, ∃ split ∈ dimensions, coefficients.all (test table split) = true ∧
        next.stacks 41 = table ∧ next.stacks 8 = split) ∧
      next.stacks 0 = [] ∧ next.regs 10 = true ∧
      Eval (command matrixPair) n base next := by
  have hc := tableContract matrixPair ctx coefficients dimensions limit tableLimit test cost
    validTable validSplit validCoefficient htableLimit hreversal hlimit hcoefficients
    hdimensions contract
  obtain ⟨n, b, hn, hi, history, heval⟩ := RecordPrograms.iterate_run_with_on tablePorts
    (tableCallback matrixPair) (tableTest coefficients dimensions test)
    (fun table => tableCost tableLimit limit (cost table) coefficients dimensions table)
    (TableEntry ctx coefficients dimensions limit tableLimit)
    (fun table _ b => Selected coefficients dimensions test table b) validTable hc tables []
    base htables hb (base.regs 8) (base.regs 9) (base.regs 10)
  have hstart : RecordPrograms.state tablePorts base (base.regs 8) (base.regs 9)
      (base.regs 10) (ProgramEncoding.encodeRecords tables ++ []) [] = base := by
    apply RecordPrograms.state_eq_self <;> simp [tablePorts, h0, h2]
  let middle := RecordPrograms.state tablePorts b false true true
    (RecordPrograms.unread (tableTest coefficients dimensions test) tables []) []
  let next := clearState middle 0
  have eclear := clear_eval middle 0
  have hrun : Eval (anyCommand tablePorts (tableCallback matrixPair)) n base middle := by
    rw [← hstart]
    simpa only [middle, success] using heval
  have hm0 : middle.stacks 0 =
      RecordPrograms.unread (tableTest coefficients dimensions test) tables [] :=
    RecordPrograms.state_source tablePorts b false true true _ []
  refine ⟨_, next, ?_, ?_, ?_, ?_, hrun.seq eclear⟩
  · have hlen := unread_length_le (tableTest coefficients dimensions test) tables
    change n + (2 * (middle.stacks 0).length + 3) ≤ _
    rw [hm0]
    unfold searchCost
    omega
  · obtain ⟨table, ht, split, hs, htest, htout, hsout⟩ :=
      selected_of_history coefficients dimensions tables test history success
    refine ⟨table, ht, split, hs, htest, ?_, ?_⟩
    · simpa [next, middle, clearState, StackRoutines.clearStacks, RecordPrograms.state,
        tablePorts] using htout
    · simpa [next, middle, clearState, StackRoutines.clearStacks, RecordPrograms.state,
        tablePorts] using hsout
  · simp [next, clearState, StackRoutines.clearStacks]
  · simp [next, clearState, readRegs, middle, RecordPrograms.state, tablePorts]

end SubexponentialSAT.Subexp.BlockSearchOuter

end OAI.Algorithms
