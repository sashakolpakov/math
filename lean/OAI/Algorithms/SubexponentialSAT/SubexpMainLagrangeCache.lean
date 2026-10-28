import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLagrangeCacheControl
import OAI.Algorithms.SubexponentialSAT.SubexpMainLagrangeCacheInputs
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheProgram

namespace OAI.Algorithms

/-!
# Actual target Lagrange cache in the Main ABI

The arithmetic inputs are derived from the actual selected-ring/cache setup.
The fixed native program supplies its complete execution and basis semantics.
Old scratch and output words are erased at their measured physical cost;
all persistent inputs, source-field arrays, and other masters are preserved.
-/

namespace SubexponentialSAT.SubexpMainLagrangeCache

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLayoutPorts (Allocation ordinary master)
open SubexpLiftRing SubexpQuarticRing

abbrev Coefficient (p D : ℕ) := Quad (Word (baseWidth p (D + 1)))

def cacheBytes (p D : ℕ) [Fact p.Prime] (rows : List (List (Coefficient p D))) : List Bool :=
  Subexp.FactorPacketCoordinates.cacheBytes
    (SubexpLagrangeCacheLoop.encodeRows p (D + 1) rows)

def RowsCorrect (p D : ℕ) [Fact p.Prime] (rows : List (List (Coefficient p D))) : Prop :=
  List.Forall₂ (SubexpLagrangeCacheRowCorrectness.Correct p (D + 1)) rows (List.range p)

def runtimeBound {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : ℕ :=
  prepareCost ((procedure er alloc).project a) +
    SubexpLagrangeCacheProgram.runtimeBound (sourceInputs a) + 758

theorem execution {er es : ℕ} (alloc : Allocation es) (a b : MainState er es)
    (p D : ℕ) [Fact p.Prime] (hcache : SubexpMainCacheSetup.Result alloc a b p D)
    (hp : BinaryArithmetic.toNat (a.stacks (persistent es 6)) = p)
    (hprecision : BinaryArithmetic.toNat (a.stacks (persistent es 22)) = D + 1)
    (hexp : BinaryArithmetic.toNat (a.stacks (persistent es 29)) = p ^ 4 - 2) :
    ∃ n ≤ runtimeBound alloc b, ∃ e rows,
      Eval (procedure er alloc).invoke n b e ∧
      Result alloc b e (cacheBytes p D rows) ∧ RowsCorrect p D rows := by
  have hinputs := inputs_valid p D hcache hp hprecision hexp
  obtain ⟨rf, rows, hn, hrows⟩ := SubexpLagrangeCacheProgram.program_correct p (D + 1)
    (targetData p D).modulus (Nat.zero_lt_succ D) (sourceInputs b)
    (targetData p D).reduction (targetData p D).zero (targetData p D).one
    (SubexpPreparedQuarticSetup.minusOne p (D + 1)) hinputs
    (targetData_reduction p D) (targetData_zero p D) (targetData_one p D)
    (targetData_minusOne p D) (prepared ((procedure er alloc).project b)).regs
  obtain ⟨n, hbound, htrace⟩ := hn
  let out := SubexpLagrangeCacheProgram.outputState p (D + 1) (sourceInputs b) rows rf
  have hlift := lift_trace alloc b out (cacheBytes p D rows) htrace rfl
  refine ⟨prepareCost ((procedure er alloc).project b) + (n + 757) + 1, ?_,
    (procedure er alloc).install b (finished out), rows, hlift.1, hlift.2, hrows⟩
  unfold runtimeBound
  omega

theorem program_runsIn {er es : ℕ} (alloc : Allocation es) (a b : MainState er es)
    (p D : ℕ) [Fact p.Prime] (hcache : SubexpMainCacheSetup.Result alloc a b p D)
    (hp : BinaryArithmetic.toNat (a.stacks (persistent es 6)) = p)
    (hprecision : BinaryArithmetic.toNat (a.stacks (persistent es 22)) = D + 1)
    (hexp : BinaryArithmetic.toNat (a.stacks (persistent es 29)) = p ^ 4 - 2) :
    ∃ e rows, RunsIn (program er alloc) (runtimeBound alloc b)
      (b.withPC (some (program er alloc).entry)) (e.withPC none) ∧
      Result alloc b e (cacheBytes p D rows) ∧ RowsCorrect p D rows := by
  obtain ⟨n, hn, e, rows, he, hr, hs⟩ := execution alloc a b p D hcache hp hprecision hexp
  refine ⟨e, rows, ⟨n, hn, ?_⟩, hr, hs⟩
  cases he with
  | call _ htrace => exact htrace

theorem primitive_execution {er es : ℕ} (alloc : Allocation es) (a b : MainState er es)
    (p D : ℕ) [Fact p.Prime] (hcache : SubexpMainCacheSetup.Result alloc a b p D)
    (hp : BinaryArithmetic.toNat (a.stacks (persistent es 6)) = p)
    (hprecision : BinaryArithmetic.toNat (a.stacks (persistent es 22)) = D + 1)
    (hexp : BinaryArithmetic.toNat (a.stacks (persistent es 29)) = p ^ 4 - 2) :
    ∃ e rows, Computation.RunsIn (primitive (program er alloc)).step
      (primitiveOverhead (program er alloc) * runtimeBound alloc b)
      (primitiveCfg (program er alloc) (b.withPC (some (program er alloc).entry)))
      (primitiveCfg (program er alloc) (e.withPC none)) ∧
      Result alloc b e (cacheBytes p D rows) ∧ RowsCorrect p D rows := by
  obtain ⟨e, rows, ht, hr, hs⟩ := program_runsIn alloc a b p D hcache hp hprecision hexp
  exact ⟨e, rows, BitProgram.primitive_execution _ ht, hr, hs⟩

theorem runtimeBound_le {er es : ℕ} (alloc : Allocation es) (a : MainState er es) (W : ℕ)
    (hw : ∀ i, inputIndex i = none → (a.stacks (stackMap alloc i)).length ≤ W) :
    runtimeBound alloc a ≤ 248 * (2 * W + 3) +
      SubexpLagrangeCacheProgram.runtimeBound (sourceInputs a) + 758 := by
  have hc := prepareCost_le ((procedure er alloc).project a) W hw
  unfold runtimeBound
  omega

theorem runtimeBound_polynomial {er es : ℕ} (alloc : Allocation es)
    (a : MainState er es) (W : ℕ)
    (hw : ∀ i, inputIndex i = none → (a.stacks (stackMap alloc i)).length ≤ W)
    (hp : SubexpLagrangeCachePreparation.primeValue (sourceInputs a) ≤ W)
    (hm : CounterPrograms.value (sourceInputs a).precision ≤ W)
    (he : BinaryArithmetic.toNat (sourceInputs a).exponent ≤ W)
    (hl : SubexpLagrangeCachePreparation.inputLength (sourceInputs a) ≤ W) :
    runtimeBound alloc a ≤ 248 * (2 * W + 3) + 100000000 * (1 + 4 * W)^8 + 758 := by
  apply (runtimeBound_le alloc a W hw).trans
  have hscale : 1 + SubexpLagrangeCachePreparation.primeValue (sourceInputs a) +
      CounterPrograms.value (sourceInputs a).precision +
      BinaryArithmetic.toNat (sourceInputs a).exponent +
      SubexpLagrangeCachePreparation.inputLength (sourceInputs a) ≤ 1 + 4 * W := by omega
  unfold SubexpLagrangeCacheProgram.runtimeBound SubexpLagrangeCacheCost.runtimeBound
  gcongr

theorem rows_length {p D : ℕ} [Fact p.Prime] {rows : List (List (Coefficient p D))}
    (h : RowsCorrect p D rows) : rows.length = p := by
  simpa only [List.length_range] using h.length_eq

theorem row_lengths {p D : ℕ} [Fact p.Prime] {rows : List (List (Coefficient p D))}
    (h : RowsCorrect p D rows) : ∀ row ∈ rows, row.length = p := by
  change List.Forall₂ (SubexpLagrangeCacheRowCorrectness.Correct p (D + 1)) rows _ at h
  generalize hindices : List.range p = indices at h
  clear hindices
  induction h with
  | nil => simp
  | @cons a b as bs hab htail ih =>
    intro row hrow
    rcases List.mem_cons.mp hrow with rfl | hrow
    · exact hab.1
    · exact ih row hrow

theorem cacheBytes_length {p D : ℕ} [Fact p.Prime] {rows : List (List (Coefficient p D))}
    (h : RowsCorrect p D rows) :
    (cacheBytes p D rows).length = SubexpLagrangeCacheCost.cacheSize p (baseWidth p (D + 1)) := by
  have hr : ∀ r ∈ SubexpLagrangeCacheLoop.encodeRows p (D + 1) rows, r.length = p := by
    intro r hmem
    obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp hmem
    simpa using row_lengths h xs hxs
  have hw : ∀ r ∈ SubexpLagrangeCacheLoop.encodeRows p (D + 1) rows,
      ∀ w ∈ r, w.length = 4 * baseWidth p (D + 1) := by
    intro r hr w hw
    obtain ⟨xs, _, rfl⟩ := List.mem_map.mp hr
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hw
    exact SubexpFlatAdd.encode_length x
  unfold cacheBytes
  rw [SubexpLagrangeCacheSize.cacheBytes_length _ p (4 * baseWidth p (D + 1)) hr hw]
  simp only [SubexpLagrangeCacheLoop.encodeRows, List.length_map, rows_length h]
  unfold SubexpLagrangeCacheCost.cacheSize
  ring

theorem Result.output_length {er es : ℕ} {alloc : Allocation es} {a b : MainState er es}
    {p D : ℕ} [Fact p.Prime] {rows : List (List (Coefficient p D))}
    (h : Result alloc a b (cacheBytes p D rows)) (hr : RowsCorrect p D rows) :
    (b.stacks (master alloc 28)).length =
      SubexpLagrangeCacheCost.cacheSize p (baseWidth p (D + 1)) := by
  rw [h.output, cacheBytes_length hr]

end SubexponentialSAT.SubexpMainLagrangeCache

end OAI.Algorithms
