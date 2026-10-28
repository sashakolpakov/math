import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.FactorPacketCoordinates

namespace OAI.Algorithms

/-!
# Exact size of the encoded Lagrange cache

These bounds concern the bytes emitted by the actual nested record encoder.
The outer row order does not affect its length, including for nonuniform rows.
-/

namespace SubexponentialSAT.SubexpLagrangeCacheSize

open Subexp.FactorPacketCoordinates

/-- A list of equal-width payloads, including every record tag and terminator. -/
theorem encodeList_length {α : Type*} (encode : α → List Bool)
    (xs : List α) (W : ℕ) (hwidth : ∀ x ∈ xs, (encode x).length = W) :
    (Encoding.encodeList encode xs).length = xs.length * (2 * W + 2) + 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := hwidth x (by simp)
      have ht := ih (fun y hy => hwidth y (by simp [hy]))
      rw [Encoding.length_encodeList_cons, hx, ht, List.length_cons]
      ring

/-- Exact byte length for any number of rows, each with `p` words of width `W`. -/
theorem cacheBytes_length (cache : List (List (List Bool))) (p W : ℕ)
    (hrows : ∀ row ∈ cache, row.length = p)
    (hwords : ∀ row ∈ cache, ∀ word ∈ row, word.length = W) :
    (cacheBytes cache).length =
      cache.length * (2 * (p * (2 * W + 2) + 1) + 2) + 1 := by
  have hwidth : ∀ rowBits ∈ cache.map (Encoding.encodeList id),
      rowBits.length = p * (2 * W + 2) + 1 := by
    intro rowBits hrowBits
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hrowBits
    rw [encodeList_length id row W (hwords row hrow), hrows row hrow]
  simpa only [cacheBytes, ProgramEncoding.encodeRecords, List.length_map] using
    encodeList_length id (cache.map (Encoding.encodeList id))
      (p * (2 * W + 2) + 1) hwidth

/-- Reversing rows preserves the actual encoded length, with no width premise. -/
@[simp] theorem cacheBytes_reverse_length (cache : List (List (List Bool))) :
    (cacheBytes cache.reverse).length = (cacheBytes cache).length := by
  simp [cacheBytes, ProgramEncoding.encodeRecords_length]

theorem cacheBytes_reverse_length_of_uniform (cache : List (List (List Bool)))
    (p W : ℕ) (hrows : ∀ row ∈ cache, row.length = p)
    (hwords : ∀ row ∈ cache, ∀ word ∈ row, word.length = W) :
    (cacheBytes cache.reverse).length =
      cache.length * (2 * (p * (2 * W + 2) + 1) + 2) + 1 := by
  rw [cacheBytes_reverse_length, cacheBytes_length cache p W hrows hwords]

/-- Simplification of the two serialized lengths charged by `reverse_run`. -/
theorem reverseCost_eq (cache : List (List (List Bool))) :
    10 * (cacheBytes cache).length + 6 * (cacheBytes cache.reverse).length + 8 =
      16 * (cacheBytes cache).length + 8 := by
  rw [cacheBytes_reverse_length]
  ring

theorem reverseCost_uniform (cache : List (List (List Bool))) (p W : ℕ)
    (hrows : ∀ row ∈ cache, row.length = p)
    (hwords : ∀ row ∈ cache, ∀ word ∈ row, word.length = W) :
    10 * (cacheBytes cache).length + 6 * (cacheBytes cache.reverse).length + 8 =
      16 * (cache.length * (2 * (p * (2 * W + 2) + 1) + 2) + 1) + 8 := by
  rw [reverseCost_eq, cacheBytes_length cache p W hrows hwords]

end SubexponentialSAT.SubexpLagrangeCacheSize

end OAI.Algorithms
