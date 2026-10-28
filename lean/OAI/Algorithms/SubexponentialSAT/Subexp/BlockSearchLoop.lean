import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockZeroProgram

namespace OAI.Algorithms

/-!
# Concrete nested control of the universal-block basis search

The matrix-product command is a fixed finite subroutine supplied by
`MatrixPairProgram`. All tuple arrays and split positions are runtime data.
The three loops scan tables, splits, and coefficients, respectively.
-/

namespace SubexponentialSAT.Subexp.BlockSearchLoop

open BitProgram StructuredCalls BlockSearchProgram

abbrev sequence (commands : List (Cmd 24 42)) : Cmd 24 42 :=
  commands.foldr Cmd.seq (.base .skip)

abbrev atom (a : StructuredProgram.Atom 24 42) : Cmd 24 42 := .base (.atom a)

abbrev clear (src : Fin 42) : Cmd 24 42 :=
  .call (StackRoutines.clearProgram src (21 : Fin 24) 22)

abbrev copy (src dst : Fin 42) : Cmd 24 42 :=
  .call (StackRoutines.copyProgram src dst 9 (21 : Fin 24) 22)

abbrev transfer (src dst : Fin 42) : Cmd 24 42 :=
  .call (StackRoutines.transferProgram src dst (21 : Fin 24) 22)

def smallRegisters (i : Fin 3) : Fin 24 := Fin.castAdd 21 i

abbrev zeroAt (src : Fin 42) : Cmd 24 42 :=
  .call (ProgramLinking.liftProgram BlockZeroProgram.program smallRegisters (fun _ => src))

abbrev skipPrefix : Cmd 24 42 :=
  .call (ProgramLinking.liftProgram BlockZeroProgram.skipProgram smallRegisters ![22, 23])

def classifyRegisters : Fin 5 → Fin 24 := ![17, 18, 19, 20, 16]

abbrev classify : Cmd 24 42 :=
  .call (ProgramLinking.liftProgram BlockZeroProgram.classifyProgram classifyRegisters
    (fun _ => (22 : Fin 42)))

/-- Copying preserves the vector used by the second matrix product. -/
abbrev zeroFrom (src : Fin 42) (flag : Fin 24) : Cmd 24 42 :=
  sequence [copy src 22, zeroAt 22, atom (.copy flag 2)]

/-- Skip the saved split number of complete coefficient frames, then test
the remaining scalar words. Both the split and full coefficients survive. -/
abbrev tailZero : Cmd 24 42 :=
  sequence [copy 8 22, copy 40 23, skipPrefix, zeroAt 23, atom (.copy 19 2)]

def coefficientPorts : SavedPorts 24 42 where
  toPorts := ⟨14, 15, 16, 6, 7, by decide, by decide, by decide, by decide⟩
  saved := 14
  temporary := 9
  saved_ne_source := by decide
  saved_ne_payload := by decide
  temporary_ne_source := by decide
  temporary_ne_payload := by decide
  saved_ne_temporary := by decide

def dimensionPorts : SavedPorts 24 42 where
  toPorts := ⟨11, 12, 13, 3, 4, by decide, by decide, by decide, by decide⟩
  saved := 12
  temporary := 9
  saved_ne_source := by decide
  saved_ne_payload := by decide
  temporary_ne_source := by decide
  temporary_ne_payload := by decide
  saved_ne_temporary := by decide

def tablePorts : RecordPrograms.Ports 24 42 :=
  ⟨8, 9, 10, 0, 2, by decide, by decide, by decide, by decide⟩

/-- The supplied matrix command computes y=Cx and z=My on fixed work ports.
The rest of this callback uses only concrete copying and Boolean programs. -/
abbrev coefficientCallback (matrixPair : Cmd 24 42) : Cmd 24 42 :=
  sequence [transfer 7 34, copy 41 33, copy 10 37, matrixPair,
    zeroFrom 34 17, zeroFrom 40 18, tailZero, zeroFrom 30 20, classify,
    clear 30, clear 34, clear 40, atom (.set 14 false), atom (.set 15 true)]

/-- The current split is copied into persistent output metadata before its
universal coefficient scan. It remains there when the scan succeeds. -/
abbrev dimensionCallback (matrixPair : Cmd 24 42) : Cmd 24 42 :=
  sequence [clear 8, copy 4 8,
    savedAllCommand coefficientPorts (coefficientCallback matrixPair),
    clear 4, atom (.copy 13 16), atom (.set 11 false), atom (.set 12 true)]

/-- The current table is installed in forward frame order and retained while
the complete split enumeration is scanned. -/
abbrev tableCallback (matrixPair : Cmd 24 42) : Cmd 24 42 :=
  sequence [clear 41, transfer 2 41,
    savedAnyCommand dimensionPorts (dimensionCallback matrixPair),
    atom (.copy 10 13), atom (.set 8 false), atom (.set 9 true)]

abbrev command (matrixPair : Cmd 24 42) : Cmd 24 42 :=
  .seq (anyCommand tablePorts (tableCallback matrixPair)) (clear 0)

/-- A finite instruction table whose only parameter is another fixed finite
instruction table. It has no dimension- or prime-dependent control labels. -/
abbrev program (matrixPair : Cmd 24 42) :=
  compiled (command matrixPair) 0 41

/-- Persistent physical inputs of the two matrix-product calls. -/
structure Context where
  modulus : List Bool
  zeroWord : List Bool
  matrix : List Bool
  rowCount : List Bool
  dimension : List Bool

/-- All work stacks needed by one coefficient test are empty at its boundary. -/
def WorkReady (a : State 24 42) : Prop :=
  a.stacks 9 = [] ∧
  ∀ j : Fin 42, 22 ≤ j.val → j ≠ 27 → j ≠ 36 → j ≠ 38 → j ≠ 39 → j ≠ 41 →
    a.stacks j = []

def CoefficientEntry (ctx : Context) (table split : List Bool) (a : State 24 42) : Prop :=
  a.stacks 27 = ctx.modulus ∧ a.stacks 36 = ctx.zeroWord ∧
  a.stacks 38 = ctx.matrix ∧ a.stacks 39 = ctx.rowCount ∧
  a.stacks 10 = ctx.dimension ∧ a.stacks 41 = table ∧ a.stacks 8 = split ∧ WorkReady a

theorem coefficientEntry_of_stacks_eq (ctx : Context) (table split : List Bool)
    {a b : State 24 42} (h : b.stacks = a.stacks) (ha : CoefficientEntry ctx table split a) :
    CoefficientEntry ctx table split b := by
  simpa only [CoefficientEntry, WorkReady, h] using ha

/-- The arithmetic callback must frame both parent iterators. This contract
is an actual execution obligation for the concrete coefficient code above. -/
abbrev CoefficientContract (matrixPair : Cmd 24 42) (ctx : Context) (table split : List Bool)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (valid : List Bool → Prop) : Prop :=
  ∀ (bits tail : List Bool) (base : State 24 42), valid bits →
    CoefficientEntry ctx table split base →
    ∃ n next, n ≤ cost bits ∧ next.stacks = base.stacks ∧
      (∀ j : Fin 24, 8 ≤ j.val → j.val ≤ 13 → next.regs j = base.regs j) ∧
      Eval (coefficientCallback matrixPair) n
        (RecordPrograms.state coefficientPorts.toPorts base false true false tail bits.reverse)
        (RecordPrograms.state coefficientPorts.toPorts next false true (test bits) tail [])

theorem coefficientContract_scan (matrixPair : Cmd 24 42) (ctx : Context)
    (table split : List Bool) (test : List Bool → Bool) (cost : List Bool → ℕ)
    (valid : List Bool → Prop)
    (h : CoefficientContract matrixPair ctx table split test cost valid) :
    RecordPrograms.CallbackContractWithOn coefficientPorts.toPorts
      (coefficientCallback matrixPair) test cost (CoefficientEntry ctx table split)
      (fun _ a b => b.stacks = a.stacks ∧
        ∀ j : Fin 24, 8 ≤ j.val → j.val ≤ 13 → b.regs j = a.regs j) valid := by
  intro bits tail base hv hb
  obtain ⟨n, next, hn, hs, hr, he⟩ := h bits tail base hv hb
  exact ⟨n, next, hn, coefficientEntry_of_stacks_eq ctx table split hs hb, ⟨hs,hr⟩, he⟩

/-- A complete coefficient scan frames both enclosing loops, including their
unread serialized tails. The copied working enumeration is empty on exit. -/
theorem coefficientScan_eval (matrixPair : Cmd 24 42) (ctx : Context)
    (table split : List Bool) (test : List Bool → Bool) (cost : List Bool → ℕ)
    (valid : List Bool → Prop)
    (contract : CoefficientContract matrixPair ctx table split test cost valid)
    (records : List (List Bool)) (base : State 24 42)
    (hv : ∀ bits ∈ records, valid bits) (hb : CoefficientEntry ctx table split base)
    (hs : base.stacks 14 = ProgramEncoding.encodeRecords records)
    (h6 : base.stacks 6 = []) (h7 : base.stacks 7 = []) :
    ∃ n next,
      n ≤ 9 * (ProgramEncoding.encodeRecords records).length +
        RecordPrograms.budget (fun bits => cost bits + 2) records + 14 ∧
      next.stacks = base.stacks ∧
      (∀ j : Fin 24, 8 ≤ j.val → j.val ≤ 13 → next.regs j = base.regs j) ∧
      next.regs 16 = records.all test ∧
      Eval (savedAllCommand coefficientPorts (coefficientCallback matrixPair)) n base next := by
  let inv := fun a : State 24 42 => CoefficientEntry ctx table split a ∧
    a.stacks = base.stacks ∧ ∀ j : Fin 24, 8 ≤ j.val → j.val ≤ 13 → a.regs j = base.regs j
  have hc : RecordPrograms.CallbackContractOn coefficientPorts.toPorts
      (coefficientCallback matrixPair) test cost inv valid := by
    intro bits tail a hbits ha
    obtain ⟨n, next, hn, hst, hreg, he⟩ := contract bits tail a hbits ha.1
    refine ⟨n, next, hn, ?_, he⟩
    exact ⟨coefficientEntry_of_stacks_eq ctx table split hst ha.1, hst.trans ha.2.1,
      fun j hj hk => (hreg j hj hk).trans (ha.2.2 j hj hk)⟩
  have htemp : base.stacks coefficientPorts.temporary = [] := hb.2.2.2.2.2.2.2.1
  obtain ⟨n, b, hn, hi, he⟩ := savedAllCommand_eval coefficientPorts
    (coefficientCallback matrixPair) test cost inv valid hc records base hv
    ⟨hb, rfl, fun _ _ _ => rfl⟩ hs htemp (base.regs 14) (base.regs 15) (base.regs 16)
  let next := RecordPrograms.state coefficientPorts.toPorts b false true (records.all test) [] []
  have hstart : RecordPrograms.state coefficientPorts.toPorts base
      (base.regs 14) (base.regs 15) (base.regs 16) [] [] = base := by
    apply RecordPrograms.state_eq_self <;> simp [coefficientPorts, h6, h7]
  refine ⟨n, next, hn, ?_, ?_, ?_, ?_⟩
  · funext j
    change (Function.update (Function.update b.stacks 6 []) 7 []) j = base.stacks j
    rw [hi.2.1]
    by_cases hj : j = 6 <;> by_cases hk : j = 7 <;> subst_vars <;> simp_all
  · intro j hj hk
    have h14 : j ≠ 14 := by intro h; subst j; change 14 ≤ 13 at hk; omega
    have h15 : j ≠ 15 := by intro h; subst j; change 15 ≤ 13 at hk; omega
    have h16 : j ≠ 16 := by intro h; subst j; change 16 ≤ 13 at hk; omega
    change (RecordPrograms.state coefficientPorts.toPorts b false true
      (records.all test) [] []).regs j = _
    rw [RecordPrograms.state_register_frame _ _ _ _ _ _ _ j h14 h15 h16]
    exact hi.2.2 j hj hk
  · exact RecordPrograms.state_found coefficientPorts.toPorts b false true
      (records.all test) [] []
  · simpa only [hstart] using he

end SubexponentialSAT.Subexp.BlockSearchLoop

end OAI.Algorithms
