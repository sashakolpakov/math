import OAI.NumberTheory.PadicHodge.IntegralComparison.MixedOrbitNewton
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FilteredEndomorphismDifference
import Mathlib.Algebra.BigOperators.Fin

/-! # Family Newton -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FamilyNewton.Family

/-! Ordered Newton expansions for arbitrary finite families. Neither the
endomorphisms nor their differences need commute. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Finset

variable {G : Type*} [AddCommGroup G]

def ordered : {r : ℕ} → (Fin r → AddMonoid.End G) → (Fin r → ℕ) → AddMonoid.End G
  | 0, _, _ => 1
  | r + 1, T, a => T 0 ^ a 0 * ordered (fun i : Fin r => T i.succ) (fun i => a i.succ)

def boxSum {M : Type*} [AddCommMonoid M] :
    {r : ℕ} → (Fin r → ℕ) → ((Fin r → ℕ) → M) → M
  | 0, _, c => c Fin.elim0
  | r + 1, b, c => ∑ i ∈ range (b 0),
      boxSum (fun j : Fin r => b j.succ) (fun a => c (Fin.cons i a))

theorem boxSum_congr {M : Type*} [AddCommMonoid M] {r : ℕ}
    (b : Fin r → ℕ) {c e : (Fin r → ℕ) → M} (h : ∀ a, c a = e a) :
    Family.boxSum b c = Family.boxSum b e := by
  congr 1
  exact funext h

theorem boxSum_zero {M : Type*} [AddCommMonoid M] {r : ℕ}
    (b : Fin r → ℕ) (c : (Fin r → ℕ) → M) (h : ∀ a, c a = 0) :
    Family.boxSum b c = 0 := by
  induction r with
  | zero => exact h _
  | succ r ih =>
    apply Finset.sum_eq_zero
    intro i _
    exact ih _ _ (fun a => h (Fin.cons i a))

theorem mul_boxSum {r : ℕ} (b : Fin r → ℕ) (c : (Fin r → ℕ) → ℚ) (q : ℚ) :
    q * Family.boxSum b c = Family.boxSum b (fun a => q * c a) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change q * ∑ i ∈ range (b 0), _ = _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => ih _ _)

theorem boxSum_eq_of_support {r : ℕ} (b e : Fin r → ℕ) (c : (Fin r → ℕ) → ℚ)
    (h : ∀ a, (∃ i, b i ≤ a i ∨ e i ≤ a i) → c a = 0) :
    Family.boxSum b c = Family.boxSum e c := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change (∑ i ∈ range (b 0), Family.boxSum (fun j : Fin r => b j.succ)
      (fun a => c (Fin.cons i a))) = _
    have ht (i : ℕ) : Family.boxSum (fun j : Fin r => b j.succ) (fun a => c (Fin.cons i a)) =
        Family.boxSum (fun j : Fin r => e j.succ) (fun a => c (Fin.cons i a)) := by
      apply ih
      intro a ha
      obtain ⟨j, hj⟩ := ha
      exact h _ ⟨j.succ, by simpa using hj⟩
    simp_rw [ht]
    let f := fun i => Family.boxSum (fun j : Fin r => e j.succ) (fun a => c (Fin.cons i a))
    have hf (i : ℕ) (hi : b 0 ≤ i ∨ e 0 ≤ i) : f i = 0 :=
      boxSum_zero _ _ (fun a => h _ ⟨0, by simpa using hi⟩)
    change ∑ i ∈ range (b 0), f i = ∑ i ∈ range (e 0), f i
    calc
      _ = ∑ i ∈ range (max (b 0) (e 0)), f i := by
        apply Finset.sum_subset (range_mono (le_max_left _ _))
        intro i _ hi
        exact hf i (Or.inl (Nat.not_lt.mp (mem_range.not.mp hi)))
      _ = _ := by
        symm
        apply Finset.sum_subset (range_mono (le_max_right _ _))
        intro i _ hi
        exact hf i (Or.inr (Nat.not_lt.mp (mem_range.not.mp hi)))

def weight {r : ℕ} (a n : Fin r → ℕ) : ℚ := ∏ i, (Nat.choose (a i) (n i) : ℚ)

theorem weight_cons {r : ℕ} (a : Fin (r + 1) → ℕ) (i : ℕ) (n : Fin r → ℕ) :
    weight a (Fin.cons i n) = (Nat.choose (a 0) i : ℚ) * weight (fun j => a j.succ) n := by
  simp [weight, Fin.prod_univ_succ]

theorem newton_full {r : ℕ} (T : Fin r → AddMonoid.End G) (φ : G →+ ℚ)
    (x : G) (a : Fin r → ℕ) :
    φ (Family.ordered T a x) = Family.boxSum (fun i => a i + 1)
      (fun n => weight a n * φ (Family.ordered (fun i => T i - 1) n x)) := by
  induction r generalizing φ with
  | zero => simp [Family.ordered, Family.boxSum, weight]
  | succ r ih =>
    change φ ((T 0 ^ a 0) (Family.ordered (fun i : Fin r => T i.succ) (fun i => a i.succ) x)) = _
    rw [MixedOrbitNewton.orbit_newton]
    apply Finset.sum_congr rfl
    intro i _
    have hh := ih (fun j : Fin r => T j.succ)
      (φ.comp (show AddMonoid.End G from (T 0 - 1) ^ i)) (fun j => a j.succ)
    change φ (((T 0 - 1) ^ i) (Family.ordered (fun j : Fin r => T j.succ) (fun j => a j.succ) x)) = _ at hh
    rw [hh, mul_boxSum]
    apply boxSum_congr
    intro n
    dsimp only
    rw [weight_cons]
    change _ * (_ * φ _) = _ * _ * φ _
    rw [mul_assoc]
    rfl

theorem newton {r : ℕ} (T : Fin r → AddMonoid.End G) (φ : G →+ ℚ)
    (x : G) (d : ℕ)
    (hzero : ∀ n : Fin r → ℕ, d < ∑ i, n i → φ (Family.ordered (fun i => T i - 1) n x) = 0)
    (a : Fin r → ℕ) :
    φ (Family.ordered T a x) = Family.boxSum (fun _ => d + 1)
      (fun n => weight a n * φ (Family.ordered (fun i => T i - 1) n x)) := by
  rw [newton_full]
  apply boxSum_eq_of_support
  intro n hn
  obtain ⟨i, hi | hi⟩ := hn
  · have hw : weight a n = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    rw [hw, zero_mul]
  · rw [hzero n (lt_of_lt_of_le (by omega) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))), mul_zero]

theorem ordered_mem_filtration (F : ℕ → AddSubgroup G) {r : ℕ}
    (T : Fin r → AddMonoid.End G)
    (hT : ∀ i d x, x ∈ F (d + 1) → T i x ∈ F d)
    (n : Fin r → ℕ) (d : ℕ) (x : G) (hx : x ∈ F (d + ∑ i, n i)) :
    Family.ordered T n x ∈ F d := by
  induction r generalizing d with
  | zero => simpa [Family.ordered] using hx
  | succ r ih =>
    apply AlgebraicGeometry.SheafCohomology.Projective.FilteredEndomorphismDifference.endomorphism_pow_mem_filtration F (T 0) (hT 0) (n 0) d
    apply ih (fun i : Fin r => T i.succ) (fun i => hT i.succ) (fun i => n i.succ) (d + n 0)
    simpa only [Fin.sum_univ_succ, Nat.add_assoc] using hx

theorem ordered_eq_zero_of_filtration (F : ℕ → AddSubgroup G) (hF : F 0 = ⊥)
    {r : ℕ} (T : Fin r → AddMonoid.End G)
    (hT : ∀ i d x, x ∈ F (d + 1) → T i x ∈ F d)
    (n : Fin r → ℕ) (x : G) (hx : x ∈ F (∑ i, n i)) : Family.ordered T n x = 0 := by
  have h := ordered_mem_filtration F T hT n 0 x (by simpa using hx)
  simpa only [hF, AddSubgroup.mem_bot] using h

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FamilyNewton.Family
