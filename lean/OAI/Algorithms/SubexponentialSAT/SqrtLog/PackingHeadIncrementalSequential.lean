import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadIncrementalCounts

namespace OAI.Algorithms

/-! Heads-first sequential ABI for the incremental physical head scorer. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadIncremental

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators

section Sequential
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ} [NeZero r]

def prefixOverlap (z : Word r Q) (fixed : List (Word r Q)) : ℕ :=
  (fixed.map (fun w => ∑ t : Fin Q, if z t = w t then 1 else 0)).sum

omit [NeZero r] in
@[simp] theorem prefixOverlap_reverse (z : Word r Q) (fixed : List (Word r Q)) :
    prefixOverlap z fixed.reverse = prefixOverlap z fixed := by
  simp [prefixOverlap]

def sequentialHeadCount (alphabet : List (Word r Q)) (pairs : List (I × I))
    (vertices : List V) (factors : List E) (default : Word r Q)
    (n : ℕ) (fixed : List (Word r Q)) : ℕ :=
  (PackingProgram.unweightedCounts ivar factor alphabet
    (pairs.map Sum.inl ++ headTerms (I := I) (Q := Q) vertices)
    (headsFirstIndices vertices factors) (List.range' fixed.length n)
    (decode default fixed)).2

omit [Fintype V] [Fintype E] in
private theorem headPosition_injective (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) :
    Function.Injective (fun v : V => indexCode (headsFirstIndices vertices factors) (.inl v)) := by
  intro v u h
  apply idxOf_injective vertices hv
  simpa only [headsFirst_index_head vertices factors _ (hv _)] using h

omit [Fintype V] [Fintype E] in
private theorem headPosition_exists (vertices : List V) (factors : List E)
    (hvn : vertices.Nodup) (p : ℕ) (hp : p < vertices.length) :
    ∃ v : V, indexCode (headsFirstIndices vertices factors) (.inl v) = p := by
  have hm : p ∈ vertices.map (indexCode vertices) := by
    rw [map_idxOf_eq_range vertices hvn]
    exact List.mem_range.mpr hp
  obtain ⟨v, hv, heq⟩ := List.mem_map.mp hm
  exact ⟨v, (headsFirst_index_head vertices factors v hv).trans heq⟩

omit [Fintype I] [Fintype E] [DecidableEq I] in
/-- The exact factor is two times q^4, where q is the word-alphabet length.
The prefix is the actual reversed fixed-word store; its order does not affect
the sum. The common constant is not an input to the physical scorer. -/
theorem sequentialHead_decomposition
    (alphabet : List (Word r Q)) (haN : alphabet.Nodup) (haC : ∀ w, w ∈ alphabet)
    (pairs : List (I × I)) (vertices : List V) (factors : List E)
    (hvN : vertices.Nodup) (hvC : ∀ v, v ∈ vertices)
    (default : Word r Q) (n : ℕ) (fixed : List (Word r Q))
    (hsize : n + 1 + fixed.length = (headsFirstIndices vertices factors).length)
    (hhead : fixed.length < vertices.length) :
    ∃ C : ℚ, ∀ z : Word r Q,
      (sequentialHeadCount ivar factor alphabet pairs vertices factors default n (z :: fixed) : ℚ) =
        C + 2 * (alphabet.length : ℚ)^4 * (prefixOverlap z fixed : ℚ) := by
  obtain ⟨v0, hkey⟩ := headPosition_exists vertices factors hvN fixed.length hhead
  let position := fun v : V => indexCode (headsFirstIndices vertices factors) (.inl v)
  have hk : position v0 ∉ List.range' (fixed.length + 1) n := by
    change indexCode (headsFirstIndices vertices factors) (.inl v0) ∉ _
    rw [hkey]
    exact prefix_not_remaining fixed n fixed.length le_rfl
  obtain ⟨C, hC⟩ := headCount_decomposition alphabet haN haC position
    (headPosition_injective vertices factors hvC) (List.range' (fixed.length + 1) n)
    List.nodup_range' v0 hk (decode default fixed)
  refine ⟨C, ?_⟩
  intro z
  have hp : priorOverlap position (List.range' (fixed.length + 1) n)
      (position v0) (decode default fixed) z = prefixOverlap z fixed := by
    change priorOverlap position _ (indexCode (headsFirstIndices vertices factors) (.inl v0)) _ _ = _
    rw [hkey]
    exact priorHeadOverlap_eq_prefix vertices factors hvN hvC default z fixed n hsize hhead.le
  have hz := hC z
  rw [hp] at hz
  simpa only [sequentialHeadCount, List.length_cons, unweighted_head_eq ivar factor alphabet pairs
    vertices hvN hvC, decode_prefix_update, position, hkey] using hz

omit [Fintype I] [Fintype E] [DecidableEq I] in
/-- At the factor stage there is no candidate-dependent head contribution. -/
theorem sequentialHead_factor_constant
    (alphabet : List (Word r Q)) (haN : alphabet.Nodup) (haC : ∀ w, w ∈ alphabet)
    (pairs : List (I × I)) (vertices : List V) (factors : List E)
    (hvN : vertices.Nodup) (hvC : ∀ v, v ∈ vertices)
    (default : Word r Q) (n : ℕ) (fixed : List (Word r Q))
    (hfactor : vertices.length ≤ fixed.length) (x y : Word r Q) :
    sequentialHeadCount ivar factor alphabet pairs vertices factors default n (x :: fixed) =
      sequentialHeadCount ivar factor alphabet pairs vertices factors default n (y :: fixed) := by
  have ha : alphabet ≠ [] := by
    intro h
    simpa [h] using haC (fun _ => 0)
  have hk (v : V) : indexCode (headsFirstIndices vertices factors) (.inl v) ≠ fixed.length := by
    rw [headsFirst_index_head vertices factors v (hvC v)]
    have hlt : indexCode vertices v < vertices.length := List.idxOf_lt_length_iff.mpr (hvC v)
    omega
  simp only [sequentialHeadCount, List.length_cons, unweighted_head_eq ivar factor alphabet pairs
    vertices hvN hvC, decode_prefix_update]
  rw [headCount_update_outside alphabet ha (mean_word_color alphabet haN haC)
    _ _ List.nodup_range' fixed.length hk,
    headCount_update_outside alphabet ha (mean_word_color alphabet haN haC)
    _ _ List.nodup_range' fixed.length hk]

omit [Fintype I] [Fintype E] [DecidableEq I] in
theorem sequentialHead_order_iff
    (alphabet : List (Word r Q)) (haN : alphabet.Nodup) (haC : ∀ w, w ∈ alphabet)
    (pairs : List (I × I)) (vertices : List V) (factors : List E)
    (hvN : vertices.Nodup) (hvC : ∀ v, v ∈ vertices)
    (default : Word r Q) (n : ℕ) (fixed : List (Word r Q))
    (hsize : n + 1 + fixed.length = (headsFirstIndices vertices factors).length)
    (hhead : fixed.length < vertices.length) (x y : Word r Q) (A B ix iy : ℕ) :
    A * ix + B * sequentialHeadCount ivar factor alphabet pairs vertices factors default n (x :: fixed) ≤
      A * iy + B * sequentialHeadCount ivar factor alphabet pairs vertices factors default n (y :: fixed) ↔
    A * ix + (2 * alphabet.length^4 * B) * prefixOverlap x fixed ≤
      A * iy + (2 * alphabet.length^4 * B) * prefixOverlap y fixed := by
  obtain ⟨C, hC⟩ := sequentialHead_decomposition ivar factor alphabet haN haC pairs vertices factors
    hvN hvC default n fixed hsize hhead
  have h :
      (A : ℚ) * ix + B * sequentialHeadCount ivar factor alphabet pairs vertices factors default n (x :: fixed) ≤
        A * iy + B * sequentialHeadCount ivar factor alphabet pairs vertices factors default n (y :: fixed) ↔
      A * ix + (2 * (alphabet.length : ℚ)^4 * B) * prefixOverlap x fixed ≤
        A * iy + (2 * (alphabet.length : ℚ)^4 * B) * prefixOverlap y fixed := by
    rw [hC x, hC y]
    constructor <;> intro h <;> nlinarith
  exact_mod_cast h

end Sequential
end SubexponentialSAT.SqrtLog.PackingHeadIncremental

end OAI.Algorithms
