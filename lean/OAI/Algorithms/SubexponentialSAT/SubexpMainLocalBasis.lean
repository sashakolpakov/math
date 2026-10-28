import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLocalBasisFrame
import OAI.Algorithms.SubexponentialSAT.SubexpMainLocalBasisCode
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchExecution
import OAI.Algorithms.SubexponentialSAT.BitProgramCompile

namespace OAI.Algorithms

/-!
# The physical local-basis batch in Main

The fixed program derives unary R from persistent binary R, invokes the
native matrix/search batch, and clears the two derived counters. Composition
lemmas retain the native boundary; `execution` discharges it with the actual
batch theorem and returns the successful basis records it produced.
-/

namespace SubexponentialSAT.SubexpMainLocalBasis

open BitProgram StructuredCalls SubexpMainProgram SubexpLayoutPorts

abbrev WorkspaceReady := @SubexpMainLocalBasisFrame.WorkspaceReady
abbrev context := @SubexpMainLocalBasisFrame.context
noncomputable abbrev result := @SubexpMainLocalBasisFrame.result

def bound {er es : ℕ} (alloc : Allocation es) (hr : 16 ≤ er)
    (a : MainState er es) (width : List Bool) (nativeBound : ℕ) : ℕ :=
  SubexpLocalBasisControl.bound (context alloc hr a)
    (a.stacks (persistent es 25)) (a.stacks (master alloc 14)) width nativeBound

theorem result_stacks {er es : ℕ} (alloc : Allocation es) (hr : 16 ≤ er)
    (a : MainState er es) (output : List Bool) (ha : WorkspaceReady alloc hr a) :
    (result alloc hr a output).stacks =
      Function.update (Function.update a.stacks (ordinary alloc 111) []) (master alloc 14) output :=
  SubexpMainLocalBasisFrame.result_stacks alloc hr a output ha

/-- This composes actual traces of the fixed native table; it does not assert
the still separate mathematical search and batch correctness theorem. -/
theorem execution_of_native {er es : ℕ} (alloc : Allocation es) (hr : 16 ≤ er)
    (a : MainState er es) (width output : List Bool) (nativeBound : ℕ)
    (ha : WorkspaceReady alloc hr a)
    (hnative : ∀ rr : Fin 32 → Bool, ∃ rf,
      RunsIn Subexp.LocalBasisBatchProgram.program nativeBound
        ((Subexp.LocalBasisBatchProgram.inputState
          (SubexpLocalBasisState.derived (context alloc hr a) (a.stacks (persistent es 25))) rr).withPC
          (some Subexp.LocalBasisBatchProgram.program.entry))
        ((Subexp.LocalBasisBatchProgram.outputState
          (SubexpLocalBasisState.derived (context alloc hr a) (a.stacks (persistent es 25)))
          width output rf).withPC none)) :
    ∃ n, n ≤ bound alloc hr a width nativeBound ∧
      Eval (procedure er hr alloc).invoke n a (result alloc hr a output) := by
  obtain ⟨n, hn, ht⟩ := SubexpLocalBasisControl.program_runs_of_native
    (context alloc hr a) (a.stacks (persistent es 25)) (a.stacks (master alloc 14))
    width output (a.regs ∘ (procedure er hr alloc).registerMap) nativeBound hnative
  have hmap : (procedure er hr alloc).registerMap =
      SubexpMainLocalBasisPorts.registerMap er hr := rfl
  rw [hmap] at ht
  rw [← SubexpMainLocalBasisFrame.project_ready alloc hr a ha] at ht
  exact ⟨n, hn, Procedure.invoke_trace (procedure er hr alloc) a _ ht⟩

theorem runsIn_of_native {er es : ℕ} (alloc : Allocation es) (hr : 16 ≤ er)
    (a : MainState er es) (width output : List Bool) (nativeBound : ℕ)
    (ha : WorkspaceReady alloc hr a)
    (hnative : ∀ rr : Fin 32 → Bool, ∃ rf,
      RunsIn Subexp.LocalBasisBatchProgram.program nativeBound
        ((Subexp.LocalBasisBatchProgram.inputState
          (SubexpLocalBasisState.derived (context alloc hr a) (a.stacks (persistent es 25))) rr).withPC
          (some Subexp.LocalBasisBatchProgram.program.entry))
        ((Subexp.LocalBasisBatchProgram.outputState
          (SubexpLocalBasisState.derived (context alloc hr a) (a.stacks (persistent es 25)))
          width output rf).withPC none)) :
    RunsIn (program er hr alloc) (bound alloc hr a width nativeBound)
      (a.withPC (some (program er hr alloc).entry)) ((result alloc hr a output).withPC none) := by
  obtain ⟨n, hn, he⟩ := execution_of_native alloc hr a width output nativeBound ha hnative
  refine ⟨n, hn, ?_⟩
  cases he with
  | call _ ht => exact ht

/-- Readiness concerns the stored input words and the value of binary R.
There is no supplied unary-R word, matrix, chosen basis, or execution trace. -/
structure CanonicalInputs {er es : ℕ} (alloc : Allocation es) (hregs : 16 ≤ er)
    (a : MainState er es) (p r Q Δ : ℕ) [Fact p.Prime]
    (coefficients alphabet : List (ZMod p)) : Prop where
  types : (context alloc hregs a).types =
    (Subexp.LocalBasisBatchProgram.canonicalContext p r Q Δ coefficients alphabet).types
  modulus : (context alloc hregs a).modulus =
    (Subexp.LocalBasisBatchProgram.canonicalContext p r Q Δ coefficients alphabet).modulus
  zero : (context alloc hregs a).zero =
    (Subexp.LocalBasisBatchProgram.canonicalContext p r Q Δ coefficients alphabet).zero
  coefficientWords : (context alloc hregs a).coefficients =
    (Subexp.LocalBasisBatchProgram.canonicalContext p r Q Δ coefficients alphabet).coefficients
  counter : CounterPrograms.value (a.stacks (persistent es 25)) = coefficients.length
  colors : (context alloc hregs a).colors =
    (Subexp.LocalBasisBatchProgram.canonicalContext p r Q Δ coefficients alphabet).colors
  positions : (context alloc hregs a).positions =
    (Subexp.LocalBasisBatchProgram.canonicalContext p r Q Δ coefficients alphabet).positions
  slots : (context alloc hregs a).slots =
    (Subexp.LocalBasisBatchProgram.canonicalContext p r Q Δ coefficients alphabet).slots
  alphabet : (context alloc hregs a).alphabet =
    (Subexp.LocalBasisBatchProgram.canonicalContext p r Q Δ coefficients alphabet).alphabet

private theorem context_ext (a b : SubexpLocalBasisState.Context)
    (h1 : a.types = b.types) (h2 : a.modulus = b.modulus) (h3 : a.zero = b.zero)
    (h4 : a.coefficients = b.coefficients) (h5 : a.length = b.length)
    (h6 : a.colors = b.colors) (h7 : a.positions = b.positions) (h8 : a.slots = b.slots)
    (h9 : a.alphabet = b.alphabet) : a = b := by
  cases a
  cases b
  simp_all

theorem CanonicalInputs.derived_eq {er es : ℕ} (alloc : Allocation es) (hregs : 16 ≤ er)
    (a : MainState er es) (p r Q Δ : ℕ) [Fact p.Prime]
    (coefficients alphabet : List (ZMod p))
    (h : CanonicalInputs alloc hregs a p r Q Δ coefficients alphabet) :
    SubexpLocalBasisState.derived (context alloc hregs a) (a.stacks (persistent es 25)) =
      Subexp.LocalBasisBatchProgram.canonicalContext p r Q Δ coefficients alphabet := by
  apply context_ext
  · exact h.types
  · exact h.modulus
  · exact h.zero
  · exact h.coefficientWords
  · simp only [SubexpLocalBasisState.derived, SubexpLocalBasisState.unary,
      Subexp.LocalBasisBatchProgram.canonicalContext, Subexp.TypeIndexProgram.unary]
    rw [h.counter]
  · exact h.colors
  · exact h.positions
  · exact h.slots
  · exact h.alphabet

noncomputable def executionBound {er es : ℕ} (alloc : Allocation es) (hregs : 16 ≤ er)
    (a : MainState er es) (p : ℕ) [Fact p.Prime] {r Q Δ : ℕ}
    (hr : 0 < r) (hQ : 0 < Q) (coefficients alphabet : List (ZMod p)) : ℕ :=
  bound alloc hregs a (Subexp.TypeIndexProgram.unary (Q * r))
    (Subexp.LocalBasisBatchProgram.sourceBudget (Δ := Δ) p hr hQ coefficients alphabet)

/-- Full execution from retained Main data. The returned records contain the
successful basis tables found by the concrete nested matrix/search loops. -/
theorem execution {er es : ℕ} (alloc : Allocation es) (hregs : 16 ≤ er)
    (a : MainState er es) (p : ℕ) [Fact p.Prime] {r Q Δ : ℕ}
    (h2 : (2 : ZMod p) ≠ 0) (hr : 0 < r) (hQ : 0 < Q)
    (coefficients alphabet : List (ZMod p)) (hfull : ∀ x, x ∈ alphabet)
    (ha : WorkspaceReady alloc hregs a)
    (hinput : CanonicalInputs alloc hregs a p r Q Δ coefficients alphabet) :
    ∃ rows, Subexp.LocalBasisBatchProgram.RowsGood
        (Subexp.LocalBasisBatchProgram.GoodResult (Δ := Δ) p hr hQ coefficients) r Q rows ∧
      ∃ n, n ≤ executionBound (Δ := Δ) alloc hregs a p hr hQ coefficients alphabet ∧
        Eval (procedure er hregs alloc).invoke n a
          (result alloc hregs a
            (ProgramEncoding.encodeRecords (rows.map ProgramEncoding.encodeRecords))) := by
  have hctx := CanonicalInputs.derived_eq alloc hregs a p r Q Δ coefficients alphabet hinput
  have hn : ∀ rr : Fin 32 → Bool, ∃ rows rf,
      Subexp.LocalBasisBatchProgram.RowsGood
        (Subexp.LocalBasisBatchProgram.GoodResult (Δ := Δ) p hr hQ coefficients) r Q rows ∧
      RunsIn Subexp.LocalBasisBatchProgram.program
        (Subexp.LocalBasisBatchProgram.sourceBudget (Δ := Δ) p hr hQ coefficients alphabet)
        ((Subexp.LocalBasisBatchProgram.inputState
          (SubexpLocalBasisState.derived (context alloc hregs a) (a.stacks (persistent es 25))) rr).withPC
          (some Subexp.LocalBasisBatchProgram.program.entry))
        ((Subexp.LocalBasisBatchProgram.outputState
          (SubexpLocalBasisState.derived (context alloc hregs a) (a.stacks (persistent es 25)))
          (Subexp.TypeIndexProgram.unary (Q * r))
          (ProgramEncoding.encodeRecords (rows.map ProgramEncoding.encodeRecords)) rf).withPC none) := by
    intro rr
    rw [hctx]
    exact Subexp.LocalBasisBatchProgram.program_runsIn p h2 hr hQ coefficients alphabet hfull rr
  obtain ⟨rows, hgood, n, hbound, ht⟩ := SubexpLocalBasisControl.program_runs_exists
    (fun rows => ProgramEncoding.encodeRecords (rows.map ProgramEncoding.encodeRecords))
    (Subexp.LocalBasisBatchProgram.RowsGood
      (Subexp.LocalBasisBatchProgram.GoodResult (Δ := Δ) p hr hQ coefficients) r Q)
    (context alloc hregs a) (a.stacks (persistent es 25)) (a.stacks (master alloc 14))
    (Subexp.TypeIndexProgram.unary (Q * r)) (a.regs ∘ (procedure er hregs alloc).registerMap)
    (Subexp.LocalBasisBatchProgram.sourceBudget (Δ := Δ) p hr hQ coefficients alphabet) hn
  have hmap : (procedure er hregs alloc).registerMap =
      SubexpMainLocalBasisPorts.registerMap er hregs := rfl
  rw [hmap] at ht
  rw [← SubexpMainLocalBasisFrame.project_ready alloc hregs a ha] at ht
  exact ⟨rows, hgood, n, hbound, Procedure.invoke_trace (procedure er hregs alloc) a _ ht⟩

theorem runsIn {er es : ℕ} (alloc : Allocation es) (hregs : 16 ≤ er)
    (a : MainState er es) (p : ℕ) [Fact p.Prime] {r Q Δ : ℕ}
    (h2 : (2 : ZMod p) ≠ 0) (hr : 0 < r) (hQ : 0 < Q)
    (coefficients alphabet : List (ZMod p)) (hfull : ∀ x, x ∈ alphabet)
    (ha : WorkspaceReady alloc hregs a)
    (hinput : CanonicalInputs alloc hregs a p r Q Δ coefficients alphabet) :
    ∃ rows, Subexp.LocalBasisBatchProgram.RowsGood
        (Subexp.LocalBasisBatchProgram.GoodResult (Δ := Δ) p hr hQ coefficients) r Q rows ∧
      RunsIn (program er hregs alloc)
        (executionBound (Δ := Δ) alloc hregs a p hr hQ coefficients alphabet)
        (a.withPC (some (program er hregs alloc).entry))
        ((result alloc hregs a
          (ProgramEncoding.encodeRecords (rows.map ProgramEncoding.encodeRecords))).withPC none) := by
  obtain ⟨rows, hgood, n, hn, he⟩ := execution alloc hregs a p h2 hr hQ coefficients alphabet hfull ha hinput
  refine ⟨rows, hgood, n, hn, ?_⟩
  cases he with
  | call _ ht => exact ht

theorem primitive_runsIn {er es : ℕ} (alloc : Allocation es) (hregs : 16 ≤ er)
    (a : MainState er es) (p : ℕ) [Fact p.Prime] {r Q Δ : ℕ}
    (h2 : (2 : ZMod p) ≠ 0) (hr : 0 < r) (hQ : 0 < Q)
    (coefficients alphabet : List (ZMod p)) (hfull : ∀ x, x ∈ alphabet)
    (ha : WorkspaceReady alloc hregs a)
    (hinput : CanonicalInputs alloc hregs a p r Q Δ coefficients alphabet) :
    ∃ rows, Subexp.LocalBasisBatchProgram.RowsGood
        (Subexp.LocalBasisBatchProgram.GoodResult (Δ := Δ) p hr hQ coefficients) r Q rows ∧
      Computation.RunsIn (primitive (program er hregs alloc)).step
        (primitiveOverhead (program er hregs alloc) *
          executionBound (Δ := Δ) alloc hregs a p hr hQ coefficients alphabet)
        (primitiveCfg (program er hregs alloc) (a.withPC (some (program er hregs alloc).entry)))
        (primitiveCfg (program er hregs alloc)
          ((result alloc hregs a
            (ProgramEncoding.encodeRecords (rows.map ProgramEncoding.encodeRecords))).withPC none)) := by
  obtain ⟨rows, hgood, he⟩ := runsIn alloc hregs a p h2 hr hQ coefficients alphabet hfull ha hinput
  exact ⟨rows, hgood, BitProgram.primitive_execution _ he⟩

end SubexponentialSAT.SubexpMainLocalBasis

end OAI.Algorithms
