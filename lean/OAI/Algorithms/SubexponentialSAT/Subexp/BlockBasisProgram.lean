import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCopyProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearch
import OAI.Algorithms.SubexponentialSAT.StackEncoding

namespace OAI.Algorithms

/-!
# Copying the actual searched local basis/complement table

This module identifies the input and output of the fixed block-copy program
with the concrete arrays returned by the local finite search.  Its measured
execution begins with the encoded local table already present.  It does not
assign unit cost to constructing or encoding that table.
-/

namespace SubexponentialSAT.Subexp.BlockBasisProgram

open scoped BigOperators
open BlockSearch BlockCopyProgram StackEncoding

variable {K : Type*} [Field K] [DecidableEq K]

/-- Explicit vector-major, coordinate-minor order for a candidate tuple. -/
def candidateEntries {N : ℕ} (c : Candidate K N) : List K :=
  (List.ofFn fun i => List.ofFn (c.2 i)).flatten

omit [Field K] [DecidableEq K] in
theorem candidateEntries_length {N : ℕ} (c : Candidate K N) :
    (candidateEntries c).length = c.1.val * N := by
  simp [candidateEntries, List.length_flatten, List.map_ofFn, Function.comp_def]

/-- The kernel tuple is followed by the complementary tuple. Their lengths
remain separate input metadata; no delimiter is inserted among field entries. -/
def pairEntries {N : ℕ} (c : Candidate K N × Candidate K N) : List K :=
  candidateEntries c.1 ++ candidateEntries c.2

omit [Field K] [DecidableEq K] in
theorem pairEntries_length {N : ℕ} (c : Candidate K N × Candidate K N) :
    (pairEntries c).length = (c.1.1.val + c.2.1.val) * N := by
  simp only [pairEntries, List.length_append, candidateEntries_length, Nat.add_mul]

omit [DecidableEq K] in
/-- Independence and spanning of the searched pair determine the number of
stored vectors; this is derived from its actual correctness proof. -/
theorem dimensions_add {m N : ℕ} {M : Fin m → Fin N → K}
    {c : Candidate K N × Candidate K N} (hc : GoodPair M c) :
    c.1.1.val + c.2.1.val = N := by
  have h := Submodule.finrank_add_eq_of_isCompl hc.isCompl
  rw [hc.1.finrank_kernel, hc.finrank_complement, Module.finrank_pi,
    Fintype.card_fin] at h
  exact h

omit [DecidableEq K] in
theorem pairEntries_length_of_good {m N : ℕ} {M : Fin m → Fin N → K}
    {c : Candidate K N × Candidate K N} (hc : GoodPair M c) :
    (pairEntries c).length = N * N := by
  rw [pairEntries_length, dimensions_add hc]

def pairBits (code : BlockCode K) {N : ℕ}
    (c : Candidate K N × Candidate K N) : List Bool :=
  encodeDataStack code (pairEntries c)

omit [DecidableEq K] in
theorem pairBits_length {m N : ℕ} (code : BlockCode K)
    {M : Fin m → Fin N → K} {c : Candidate K N × Candidate K N}
    (hc : GoodPair M c) : (pairBits code c).length = N * N * code.width := by
  rw [pairBits, length_encodeDataStack, pairEntries_length_of_good hc]

/-- The semantic array is repeated once per block, in the same order as the
fixed program's repeated bitstring. -/
def blockEntries (b : ℕ) {N : ℕ} (c : Candidate K N × Candidate K N) : List K :=
  (List.replicate b (pairEntries c)).flatten

theorem copies_encode {A : Type*} (code : BlockCode A) (b : ℕ) (xs : List A) :
    copies b (encodeDataStack code xs) =
      encodeDataStack code ((List.replicate b xs).flatten) := by
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [copies_succ, ih, List.replicate_succ', List.flatten_append,
        List.flatten_cons, List.flatten_nil, List.append_nil, encodeDataStack_append]

omit [DecidableEq K] in
theorem blockEntries_length {m N : ℕ} {M : Fin m → Fin N → K}
    {c : Candidate K N × Candidate K N} (hc : GoodPair M c) (b : ℕ) :
    (blockEntries b c).length = b * (N * N) := by
  simp [blockEntries, List.length_flatten, pairEntries_length_of_good hc]

omit [DecidableEq K] in
/-- Actual fixed-instruction execution on a correct local basis/complement
table. The local table is preserved and the exact block table is output. -/
theorem pair_program_trace {m N : ℕ} (code : BlockCode K)
    {M : Fin m → Fin N → K} {c : Candidate K N × Candidate K N}
    (hc : GoodPair M c) (b : ℕ) (suffix : List Bool) :
    BitProgram.Trace program (b * (7 * (N * N * code.width) + 7) + 3)
      ((initialState b (pairBits code c) suffix).withPC (some program.entry))
      ((data false false (pairBits code c)
        (encodeDataStack code (blockEntries b c) ++ suffix) []).withPC none) := by
  have h := program_trace b (pairBits code c) suffix
  rw [pairBits_length code hc] at h
  simpa only [pairBits, blockEntries, copies_encode] using h

/-- Specialization to the exact tuple returned by the finite local search;
no independently supplied basis or dimension hypothesis is needed. -/
theorem searchedPair_program_trace {m N : ℕ} (code : BlockCode K)
    (alphabet : List K) (ha : ∀ a, a ∈ alphabet) (M : Fin m → Fin N → K)
    (b : ℕ) (suffix : List Bool) :
    BitProgram.Trace program (b * (7 * (N * N * code.width) + 7) + 3)
      ((initialState b (pairBits code (findPair alphabet ha M)) suffix).withPC
        (some program.entry))
      ((data false false (pairBits code (findPair alphabet ha M))
        (encodeDataStack code (blockEntries b (findPair alphabet ha M)) ++ suffix) []).withPC
          none) :=
  pair_program_trace code (findPair_good alphabet ha M) b suffix

/-- The same specialization in the actual compiled binary-machine semantics. -/
theorem searchedPair_program_primitive {m N : ℕ} (code : BlockCode K)
    (alphabet : List K) (ha : ∀ a, a ∈ alphabet) (M : Fin m → Fin N → K)
    (b : ℕ) (suffix : List Bool) :
    Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program *
        (b * (7 * (N * N * code.width) + 7) + 3))
      (BitProgram.primitiveCfg program
        ((initialState b (pairBits code (findPair alphabet ha M)) suffix).withPC
          (some program.entry)))
      (BitProgram.primitiveCfg program
        ((data false false (pairBits code (findPair alphabet ha M))
          (encodeDataStack code (blockEntries b (findPair alphabet ha M)) ++ suffix) []).withPC
            none)) :=
  BitProgram.primitive_trace _ (searchedPair_program_trace code alphabet ha M b suffix)

/-- Polynomial global cost for copying the exact searched table. The block
search and field-code width are visible local parameters. -/
theorem searchedPair_trace_bound {m N b D : ℕ} (code : BlockCode K)
    (alphabet : List K) (ha : ∀ a, a ∈ alphabet) (M : Fin m → Fin N → K)
    (hb : b ≤ D) :
    b * (7 * (pairBits code (findPair alphabet ha M)).length + 7) + 3 ≤
      7 * D * (N * N * code.width + 1) + 3 := by
  apply trace_bound _ hb
  exact le_of_eq (pairBits_length code (findPair_good alphabet ha M))

/-- A nonempty packed block supplies an injection from block indices into the
global coordinates, so the global factor in the runtime is derived from the
actual packing. -/
theorem blockCount_le {b D : ℕ} {U : Type*} (e : Fin b × U ↪ Fin D) (u : U) :
    b ≤ D := by
  have hinj : Function.Injective (fun i : Fin b => e (i, u)) := by
    intro i j h
    exact congrArg Prod.fst (e.injective h)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hinj

/-- The copied, searched basis table has a real binary-machine run with a
bound polynomial in the number of global coordinates. The only local size
in the bound is the proved `N² * code.width` table length. -/
theorem searchedPair_packing_primitive {m N b D : ℕ} {U : Type*}
    (code : BlockCode K) (alphabet : List K) (ha : ∀ a, a ∈ alphabet)
    (M : Fin m → Fin N → K) (e : Fin b × U ↪ Fin D) (u : U) (suffix : List Bool) :
    Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * (7 * D * (N * N * code.width + 1) + 3))
      (BitProgram.primitiveCfg program
        ((initialState b (pairBits code (findPair alphabet ha M)) suffix).withPC
          (some program.entry)))
      (BitProgram.primitiveCfg program
        ((data false false (pairBits code (findPair alphabet ha M))
          (encodeDataStack code (blockEntries b (findPair alphabet ha M)) ++ suffix) []).withPC
            none)) := by
  apply (searchedPair_program_primitive code alphabet ha M b suffix).mono
  apply Nat.mul_le_mul_left
  calc
    b * (7 * (N * N * code.width) + 7) + 3 ≤
        D * (7 * (N * N * code.width) + 7) + 3 := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (blockCount_le e u)) _
    _ = _ := by ring

end SubexponentialSAT.Subexp.BlockBasisProgram

end OAI.Algorithms
