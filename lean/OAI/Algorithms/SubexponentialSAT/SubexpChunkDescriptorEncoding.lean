import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Encoding
import OAI.Algorithms.SubexponentialSAT.ChunkPartition

namespace OAI.Algorithms

/-! Exact byte specifications for the actual chunk descriptor producer. -/

namespace SubexponentialSAT.SubexpChunkDescriptorEncoding

open Encoding

def record (bits : List Bool) : List Bool := true :: frame bits

def recordPrefix {α : Type*} (encode : α → List Bool) (xs : List α) : List Bool :=
  xs.flatMap (fun x => record (encode x))

theorem encodeList_eq_prefix {α : Type*} (encode : α → List Bool) (xs : List α) :
    encodeList encode xs = recordPrefix encode xs ++ [false] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeList, recordPrefix, record, ih, List.append_assoc]

theorem frame_replicate (n : ℕ) (bits : List Bool) :
    frame (List.replicate n true ++ bits) = List.replicate (2 * n) true ++ frame bits := by
  induction n with
  | zero => simp
  | succ n ih =>
      simpa [List.replicate_succ, frame, Nat.mul_add, List.replicate_add] using
        congrArg (fun xs => true :: true :: xs) ih

theorem width_record (n : ℕ) :
    record (List.replicate n true) = [true] ++ List.replicate (2 * n) true ++ [false] := by
  simpa [record, frame] using congrArg (List.cons true) (frame_replicate n [])

def scopeSuffix : List Bool := [true, true, true, false, true, false, true, false, false]

theorem scope_record (j : ℕ) :
    record (encodeList encodeNat [j]) =
      [true, true, true] ++ List.replicate (4 * j) true ++ scopeSuffix := by
  simp only [record, encodeList, encodeNat, frame_replicate, frame_cons, frame_nil]
  simp only [List.cons_append, List.nil_append ]
  rw [List.append_assoc, frame_replicate]
  norm_num [scopeSuffix, frame_cons, frame_nil, ← Nat.mul_assoc]

def widths (n ell : ℕ) : List ℕ :=
  (List.range (ChunkPartition.count n ell)).map (fun j => min ell (n - j * ell))

def widthShapes (n ell : ℕ) : List Bool :=
  encodeList id ((widths n ell).map (fun b => List.replicate b true))

def scopes (start count : ℕ) : List Bool :=
  encodeList (encodeList encodeNat) ((List.range' start count).map List.singleton)

@[simp] theorem widths_length (n ell : ℕ) :
    (widths n ell).length = ChunkPartition.count n ell := by simp [widths]

@[simp] theorem widths_zero {ell : ℕ} (hell : 0 < ell) : widths 0 ell = [] := by
  simp [widths, ChunkPartition.count_zero hell]

theorem count_step {n ell : ℕ} (hn : 0 < n) (hell : 0 < ell) :
    ChunkPartition.count n ell = ChunkPartition.count (n - ell) ell + 1 := by
  have hD : 0 < ChunkPartition.count n ell := (ChunkPartition.count_pos_iff hell).mpr hn
  have hu := ChunkPartition.le_count_mul (n := n - ell) hell
  have hv := ChunkPartition.le_count_mul (n := n) hell
  have h₁ : ChunkPartition.count n ell ≤ ChunkPartition.count (n - ell) ell + 1 := by
    apply (ChunkPartition.count_le_iff hell).mpr
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hD' : ChunkPartition.count n ell = (ChunkPartition.count n ell - 1) + 1 := by omega
  have h₂ : ChunkPartition.count (n - ell) ell ≤ ChunkPartition.count n ell - 1 := by
    apply (ChunkPartition.count_le_iff hell).mpr
    rw [hD', Nat.add_mul, Nat.one_mul] at hv
    omega
  omega

theorem widths_step {n ell : ℕ} (hn : 0 < n) (hell : 0 < ell) :
    widths n ell = min ell n :: widths (n - ell) ell := by
  unfold widths
  rw [count_step hn hell, List.range_succ_eq_map]
  simp only [List.map_cons, Nat.zero_mul, Nat.sub_zero, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply, Nat.succ_mul, Nat.sub_sub]
  congr 1
  omega

theorem widths_sum {n ell : ℕ} (hell : 0 < ell) : (widths n ell).sum = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n; simp [widths_zero hell]
      · rw [widths_step (by omega) hell, List.sum_cons, ih (n - ell) (by omega)]
        omega

theorem widths_positive {n ell b : ℕ} (hell : 0 < ell) (hb : b ∈ widths n ell) :
    0 < b ∧ b ≤ ell := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
  have hj' : j * ell < n := (ChunkPartition.lt_count_iff hell).mp (List.mem_range.mp hj)
  omega

def widthPrefix (n ell : ℕ) : List Bool :=
  recordPrefix (fun b => List.replicate b true) (widths n ell)

def scopePrefix (start count : ℕ) : List Bool :=
  recordPrefix (encodeList encodeNat) ((List.range' start count).map List.singleton)

@[simp] theorem widthPrefix_zero {ell : ℕ} (hell : 0 < ell) : widthPrefix 0 ell = [] := by
  simp [widthPrefix, widths_zero hell, recordPrefix]

@[simp] theorem scopePrefix_zero (start : ℕ) : scopePrefix start 0 = [] := by
  simp [scopePrefix, recordPrefix]

theorem widthPrefix_step {n ell : ℕ} (hn : 0 < n) (hell : 0 < ell) :
    widthPrefix n ell = record (List.replicate (min ell n) true) ++
      widthPrefix (n - ell) ell := by
  simp [widthPrefix, widths_step hn hell, recordPrefix]

theorem scopePrefix_step (start count : ℕ) :
    scopePrefix start (count + 1) = record (encodeList encodeNat [start]) ++
      scopePrefix (start + 1) count := by
  simp [scopePrefix, List.range'_succ, recordPrefix, List.singleton]

theorem widthShapes_eq (n ell : ℕ) : widthShapes n ell = widthPrefix n ell ++ [false] := by
  rw [widthShapes, encodeList_eq_prefix]
  simp [widthPrefix, recordPrefix, List.flatMap_map]

theorem scopes_eq (start count : ℕ) : scopes start count = scopePrefix start count ++ [false] :=
  encodeList_eq_prefix _ _

end SubexponentialSAT.SubexpChunkDescriptorEncoding

end OAI.Algorithms
