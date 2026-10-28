import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadIncrementalPair
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWordBalance

namespace OAI.Algorithms

/-! The exact candidate-dependent part of the head conditional score. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadIncremental

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open scoped BigOperators

variable {r Q : ℕ}

def priorOverlap {V : Type*} [Fintype V] (position : V → ℕ)
    (remaining : List ℕ) (key : ℕ) (ω : ℕ → Word r Q) (z : Word r Q) : ℕ :=
  ∑ t : Fin Q, ∑ v : V,
    if position v = key ∨ position v ∈ remaining then 0
    else if z t = ω (position v) t then 1 else 0

def headCount {V : Type*} [Fintype V] (alphabet : List (Word r Q))
    (position : V → ℕ) (remaining : List ℕ) (ω : ℕ → Word r Q) : ℕ :=
  ∑ t : Fin Q, ∑ v : V, ∑ u : V,
    pairCount alphabet remaining t (position v) (position u) ω

def headDelta (remaining : List ℕ) (key : ℕ) (ω : ℕ → Word r Q)
    (z : Word r Q) (t : Fin Q) (a : ℕ) : ℚ :=
  if a = key ∨ a ∈ remaining then 0 else
    (if z t = ω a t then 1 else 0) - collision t key a ω

theorem pairCount_update (alphabet : List (Word r Q)) (ha : alphabet ≠ [])
    (hbalance : ∀ (t : Fin Q) (c : Fin r),
      SubexponentialSAT.ConditionalExpectation.mean alphabet
        (fun w => if w t = c then (1 : ℚ) else 0) = 1 / (r : ℚ))
    (remaining : List ℕ) (hn : remaining.Nodup) (key : ℕ) (hk : key ∉ remaining)
    (t : Fin Q) (a b : ℕ) (ω : ℕ → Word r Q) (z : Word r Q) :
    (pairCount alphabet remaining t a b (Function.update ω key z) : ℚ) =
      (pairCount alphabet remaining t a b ω : ℚ) + (alphabet.length : ℚ)^4 *
        ((if a = key then headDelta remaining key ω z t b else 0) +
         (if b = key then headDelta remaining key ω z t a else 0)) := by
  rw [pairCount_cast alphabet ha hbalance remaining hn,
    pairCount_cast alphabet ha hbalance remaining hn]
  by_cases hak : a = key <;> by_cases hbk : b = key <;>
    by_cases hab : a = b <;> by_cases har : a ∈ remaining <;>
    by_cases hbr : b ∈ remaining <;>
    simp_all [collision, headDelta, eq_comm] <;> split_ifs <;> ring

theorem sum_headDelta {V : Type*} [Fintype V] (position : V → ℕ)
    (remaining : List ℕ) (key : ℕ) (ω : ℕ → Word r Q) (z : Word r Q) :
    (∑ t : Fin Q, ∑ v : V, headDelta remaining key ω z t (position v)) =
      (priorOverlap position remaining key ω z : ℚ) -
        (priorOverlap position remaining key ω (ω key) : ℚ) := by
  simp only [priorOverlap, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro v hv
  by_cases h : position v = key ∨ position v ∈ remaining
  · simp [headDelta, h]
  · simp [headDelta, collision, h]

/-- Both ordered orientations contribute. The self term and all terms with
unassigned partners are candidate-independent. -/
theorem headCount_update {V : Type*} [Fintype V] [DecidableEq V]
    (alphabet : List (Word r Q)) (ha : alphabet ≠ [])
    (hbalance : ∀ (t : Fin Q) (c : Fin r),
      SubexponentialSAT.ConditionalExpectation.mean alphabet
        (fun w => if w t = c then (1 : ℚ) else 0) = 1 / (r : ℚ))
    (position : V → ℕ) (hinj : Function.Injective position)
    (remaining : List ℕ) (hn : remaining.Nodup) (v0 : V)
    (hk : position v0 ∉ remaining) (ω : ℕ → Word r Q) (z : Word r Q) :
    (headCount alphabet position remaining (Function.update ω (position v0) z) : ℚ) =
      (headCount alphabet position remaining ω : ℚ) + 2 * (alphabet.length : ℚ)^4 *
        ((priorOverlap position remaining (position v0) ω z : ℚ) -
         (priorOverlap position remaining (position v0) ω (ω (position v0)) : ℚ)) := by
  simp only [headCount, Nat.cast_sum]
  simp_rw [pairCount_update alphabet ha hbalance remaining hn (position v0) hk,
    hinj.eq_iff]
  simp only [ Finset.sum_add_distrib, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ← Finset.mul_sum]
  rw [← sum_headDelta position remaining (position v0) ω z]
  ring

/-- The complete head contribution differs from the incremental overlap by
one common rational constant. The physical comparison never computes it. -/
theorem headCount_decomposition {V : Type*} [Fintype V] [DecidableEq V] [NeZero r]
    (alphabet : List (Word r Q)) (haN : alphabet.Nodup)
    (haC : ∀ w, w ∈ alphabet)
    (position : V → ℕ) (hinj : Function.Injective position)
    (remaining : List ℕ) (hn : remaining.Nodup) (v0 : V)
    (hk : position v0 ∉ remaining) (ω : ℕ → Word r Q) :
    ∃ C : ℚ, ∀ z : Word r Q,
      (headCount alphabet position remaining (Function.update ω (position v0) z) : ℚ) =
        C + 2 * (alphabet.length : ℚ)^4 *
          (priorOverlap position remaining (position v0) ω z : ℚ) := by
  have ha : alphabet ≠ [] := by
    intro h
    simpa [h] using haC (fun _ => 0)
  refine ⟨(headCount alphabet position remaining ω : ℚ) -
    2 * (alphabet.length : ℚ)^4 *
      (priorOverlap position remaining (position v0) ω (ω (position v0)) : ℚ), ?_⟩
  intro z
  rw [headCount_update alphabet ha (Packing.mean_word_color alphabet haN haC)
    position hinj remaining hn v0 hk ω z]
  ring

theorem combined_order_iff {V : Type*} [Fintype V] [DecidableEq V] [NeZero r]
    (alphabet : List (Word r Q)) (haN : alphabet.Nodup) (haC : ∀ w, w ∈ alphabet)
    (position : V → ℕ) (hinj : Function.Injective position)
    (remaining : List ℕ) (hn : remaining.Nodup) (v0 : V)
    (hk : position v0 ∉ remaining) (ω : ℕ → Word r Q)
    (x y : Word r Q) (A B ix iy : ℕ) :
    A * ix + B * headCount alphabet position remaining (Function.update ω (position v0) x) ≤
      A * iy + B * headCount alphabet position remaining (Function.update ω (position v0) y) ↔
    A * ix + (2 * alphabet.length^4 * B) * priorOverlap position remaining (position v0) ω x ≤
      A * iy + (2 * alphabet.length^4 * B) * priorOverlap position remaining (position v0) ω y := by
  obtain ⟨C, hC⟩ := headCount_decomposition alphabet haN haC position hinj remaining hn v0 hk ω
  have h :
      (A : ℚ) * ix + B * headCount alphabet position remaining (Function.update ω (position v0) x) ≤
        A * iy + B * headCount alphabet position remaining (Function.update ω (position v0) y) ↔
      A * ix + (2 * (alphabet.length : ℚ)^4 * B) * priorOverlap position remaining (position v0) ω x ≤
        A * iy + (2 * (alphabet.length : ℚ)^4 * B) * priorOverlap position remaining (position v0) ω y := by
    rw [hC x, hC y]
    constructor <;> intro h <;> nlinarith
  exact_mod_cast h

theorem headCount_update_outside {V : Type*} [Fintype V]
    (alphabet : List (Word r Q)) (ha : alphabet ≠ [])
    (hbalance : ∀ (t : Fin Q) (c : Fin r),
      SubexponentialSAT.ConditionalExpectation.mean alphabet
        (fun w => if w t = c then (1 : ℚ) else 0) = 1 / (r : ℚ))
    (position : V → ℕ) (remaining : List ℕ) (hn : remaining.Nodup)
    (key : ℕ) (hk : ∀ v, position v ≠ key) (ω : ℕ → Word r Q) (z : Word r Q) :
    headCount alphabet position remaining (Function.update ω key z) =
      headCount alphabet position remaining ω := by
  have h : (headCount alphabet position remaining (Function.update ω key z) : ℚ) =
      (headCount alphabet position remaining ω : ℚ) := by
    simp only [headCount, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro u hu
    rw [pairCount_cast alphabet ha hbalance remaining hn,
      pairCount_cast alphabet ha hbalance remaining hn]
    simp only [collision, Function.update_of_ne (hk v), Function.update_of_ne (hk u)]
  exact_mod_cast h

end SubexponentialSAT.SqrtLog.PackingHeadIncremental

end OAI.Algorithms
