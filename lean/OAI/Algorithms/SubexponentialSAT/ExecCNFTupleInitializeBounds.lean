import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFTupleInitialize

namespace OAI.Algorithms

/-!
# Arithmetic bound for the actual tuple initializer

The bound includes the decoded row count and decoded bit width, as well as
the lengths of both binary words. It therefore covers the actual nested
counter loops without treating a large encoded integer as a constant-cost
loop bound or assuming that either input word is canonical.
-/

namespace SubexponentialSAT.ExecCNFTupleInitialize

open BitProgram StructuredCalls

theorem frameBound_le_uniform (width : List Bool) (B : ℕ) (hB : 1 ≤ B)
    (hv : CounterPrograms.value width ≤ B) (hl : width.length ≤ B) :
    TupleZeroProgram.frameBound width ≤ 80 * B ^ 2 := by
  have hlinear : B ≤ B ^ 2 := by nlinarith
  have hone : 1 ≤ B ^ 2 := by nlinarith
  calc
    TupleZeroProgram.frameBound width ≤
        4 * B + (B + 1) * (16 * B + 16) + 2 * B + 5 := by
      unfold TupleZeroProgram.frameBound
      gcongr
    _ ≤ 80 * B ^ 2 := by nlinarith

theorem outerBound_le_uniform (width : List Bool) (B : ℕ) (hB : 1 ≤ B)
    (hv : CounterPrograms.value width ≤ B) (hl : width.length ≤ B) :
    TupleZeroProgram.outerBound width ≤ 96 * B ^ 2 := by
  have hf := frameBound_le_uniform width B hB hv hl
  have hlinear : B ≤ B ^ 2 := by nlinarith
  have hone : 1 ≤ B ^ 2 := by nlinarith
  unfold TupleZeroProgram.outerBound
  nlinarith

theorem prependBound_le_uniform (rows width : List Bool) (B : ℕ) (hB : 1 ≤ B)
    (hr : CounterPrograms.value rows ≤ B) (hw : CounterPrograms.value width ≤ B)
    (hrl : rows.length ≤ B) (hwl : width.length ≤ B) :
    TupleZeroProgram.prependBound rows width ≤ 176 * B ^ 3 := by
  have ho := outerBound_le_uniform width B hB hw hwl
  have hlinear : B ≤ B ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < B) (by omega : 1 ≤ 3)
  have hsquare : B ^ 2 ≤ B ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hone : 1 ≤ B ^ 3 := Nat.one_le_pow _ _ hB
  calc
    TupleZeroProgram.prependBound rows width ≤
        B * (96 * B ^ 2) + (B + 1) * (16 * B + 16) + 2 * B + 2 * B + 6 := by
      unfold TupleZeroProgram.prependBound
      gcongr
    _ ≤ 176 * B ^ 3 := by nlinarith

/-- A cubic bound on every source instruction used to initialize a candidate
tuple, including copying its binary dimensions and writing the fixed mask. -/
theorem bound_le_uniform (k : ℕ) (rows width : List Bool) (B : ℕ) (hB : 1 ≤ B)
    (hk : k ≤ B) (hr : CounterPrograms.value rows ≤ B)
    (hw : CounterPrograms.value width ≤ B) (hrl : rows.length ≤ B) (hwl : width.length ≤ B) :
    bound k rows width ≤ 256 * B ^ 3 := by
  have hp := prependBound_le_uniform rows width B hB hr hw hrl hwl
  have hlinear : B ≤ B ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < B) (by omega : 1 ≤ 3)
  have hone : 1 ≤ B ^ 3 := Nat.one_le_pow _ _ hB
  unfold bound
  omega

/-- The arithmetic estimate prices the existing finite initializer, with its
exact tuple result and all unrelated stacks preserved. -/
theorem command_eval_le_uniform (k : ℕ) (d : Data) (h : Ready d)
    (B : ℕ) (hB : 1 ≤ B) (hk : k ≤ B)
    (hr : CounterPrograms.value (d.stacks 15) ≤ B)
    (hw : CounterPrograms.value (d.stacks 20) ≤ B)
    (hrl : (d.stacks 15).length ≤ B) (hwl : (d.stacks 20).length ≤ B) :
    ∃ n e, Eval (command k) n d e ∧ n ≤ 256 * B ^ 3 ∧
      e.stacks 17 = Encoding.encodeList id (words k (d.stacks 15) (d.stacks 20)) ∧
      (∀ i : Fin 32, i ≠ 17 → e.stacks i = d.stacks i) := by
  obtain ⟨n, e, he, hn, ht, hf⟩ := command_eval k d h
  exact ⟨n, e, he, hn.trans
    (bound_le_uniform k (d.stacks 15) (d.stacks 20) B hB hk hr hw hrl hwl), ht, hf⟩

end SubexponentialSAT.ExecCNFTupleInitialize

end OAI.Algorithms
