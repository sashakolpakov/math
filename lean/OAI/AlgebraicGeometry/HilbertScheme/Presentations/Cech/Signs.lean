import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! # Signs -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.Signs.ProjectiveCech

/-! Alternating signs for the finite, ordered projective Čech complex. -/

universe u v

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]

def alternatingSign (s : Finset σ) (i : σ) : R := (-1) ^ (s.filter (· < i)).card

theorem alternatingSign_square (s : Finset σ) (i : σ) :
    alternatingSign R s i * alternatingSign R s i = 1 := by
  unfold alternatingSign
  rw [← pow_add, ← two_mul, pow_mul]
  simp

theorem alternatingSign_insert_self (s : Finset σ) (i : σ) :
    alternatingSign R (insert i s) i = alternatingSign R s i := by
  simp [alternatingSign, Finset.filter_insert]

theorem alternatingSign_erase_self (s : Finset σ) (i : σ) :
    alternatingSign R (s.erase i) i = alternatingSign R s i := by
  simp [alternatingSign, Finset.filter_erase]

theorem alternatingSign_insert_lt {s : Finset σ} {i j : σ} (hj : j ∉ s) (hji : j < i) :
    alternatingSign R (insert j s) i = -alternatingSign R s i := by
  rw [alternatingSign, Finset.filter_insert, ite_eq_left hji, Finset.card_insert_of_notMem]
  · simp [alternatingSign, pow_succ]
  · exact fun h => hj (Finset.mem_filter.mp h).1

theorem alternatingSign_insert_of_le {s : Finset σ} {i j : σ} (hij : i ≤ j) :
    alternatingSign R (insert j s) i = alternatingSign R s i := by
  simp [alternatingSign, Finset.filter_insert, not_lt.mpr hij]

theorem alternatingSign_erase_lt {s : Finset σ} {i j : σ} (hi : i ∈ s) (hij : i < j) :
    alternatingSign R s j = -alternatingSign R (s.erase i) j := by
  have h := alternatingSign_insert_lt R (s := s.erase i) (i := j)
    (Finset.notMem_erase i s) hij
  simpa only [Finset.insert_erase hi] using h

theorem alternatingSign_erase_of_le {s : Finset σ} {i j : σ} (hji : j ≤ i) :
    alternatingSign R (s.erase i) j = alternatingSign R s j := by
  simp [alternatingSign, Finset.filter_erase, not_lt.mpr hji]

theorem alternatingSign_insert_erase {s : Finset σ} {i j : σ} (hi : i ∈ s) (hj : j ∉ s) :
    alternatingSign R s j * alternatingSign R (insert j s) i =
      -(alternatingSign R s i * alternatingSign R (s.erase i) j) := by
  have hne : i ≠ j := fun h => hj (h ▸ hi)
  rcases lt_or_gt_of_ne hne with hij | hji
  · rw [alternatingSign_insert_of_le R hij.le, alternatingSign_erase_lt R hi hij]
    ring
  · rw [alternatingSign_insert_lt R hj hji, alternatingSign_erase_of_le R hji.le]
    ring

theorem alternatingSign_erase_anticommute {s : Finset σ} {i j : σ}
    (hi : i ∈ s) (hj : j ∈ s) (hne : i ≠ j) :
    alternatingSign R s i * alternatingSign R (s.erase i) j =
      -(alternatingSign R s j * alternatingSign R (s.erase j) i) := by
  rcases lt_or_gt_of_ne hne with hij | hji
  · rw [alternatingSign_erase_of_le R hij.le, alternatingSign_erase_lt R hi hij]
    ring
  · rw [alternatingSign_erase_of_le R hji.le, alternatingSign_erase_lt R hj hji]
    ring

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.Signs.ProjectiveCech
