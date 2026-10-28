import OAI.AlgebraicGeometry.SheafCohomology.Projective.EndomorphismOrbitDifference
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! # Mixed Orbit Newton -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.MixedOrbitNewton

/-! Rational-valued Newton expansion for three ordered endomorphism
orbits. Joint vanishing of the ordered differences bounds the total degree;
commutativity of the three endomorphisms is not required. -/

variable {G : Type*} [AddCommGroup G]

theorem orbit_fwdDiff (T : AddMonoid.End G) (φ : G →+ ℚ) (x : G) (r n : ℕ) :
    (fwdDiff 1)^[r] (fun k : ℕ => φ ((T ^ k) x)) n =
      φ ((T ^ n) (((T - 1) ^ r) x)) := by
  induction r generalizing n with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    change (fwdDiff 1)^[r] (fun k : ℕ => φ ((T ^ k) x)) (n + 1) -
      (fwdDiff 1)^[r] (fun k : ℕ => φ ((T ^ k) x)) n = _
    rw [ih, ih, pow_succ T n, pow_succ' (T - 1) r]
    change φ ((T ^ n) (T (((T - 1) ^ r) x))) - φ ((T ^ n) (((T - 1) ^ r) x)) =
      φ ((T ^ n) (T (((T - 1) ^ r) x) - ((T - 1) ^ r) x))
    rw [map_sub, map_sub]

theorem orbit_newton (T : AddMonoid.End G) (φ : G →+ ℚ) (x : G) (n : ℕ) :
    φ ((T ^ n) x) =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℚ) * φ (((T - 1) ^ i) x) := by
  have h := shift_eq_sum_fwdDiff_iter 1 (fun k : ℕ => φ ((T ^ k) x)) n 0
  simpa only [nsmul_eq_mul, Nat.cast_id, mul_one, zero_add, orbit_fwdDiff,
    pow_zero, AddMonoid.End.one_apply] using h

theorem choose_sum_truncate (a r : ℕ) (c : ℕ → ℚ)
    (hc : ∀ i : ℕ, r ≤ i → c i = 0) :
    (∑ i ∈ Finset.range (a + 1), (a.choose i : ℚ) * c i) =
      ∑ i ∈ Finset.range r, (a.choose i : ℚ) * c i := by
  calc
    _ = ∑ i ∈ Finset.range (max (a + 1) r), (a.choose i : ℚ) * c i := by
      apply Finset.sum_subset (Finset.range_mono (le_max_left _ _))
      intro i _ hi
      have hai : a < i := by have := Finset.mem_range.not.mp hi; omega
      rw [Nat.choose_eq_zero_of_lt hai, Nat.cast_zero, zero_mul]
    _ = _ := by
      symm
      apply Finset.sum_subset (Finset.range_mono (le_max_right _ _))
      intro i _ hi
      rw [hc i (Nat.not_lt.mp (Finset.mem_range.not.mp hi)), mul_zero]

def coefficient (T U V : AddMonoid.End G) (φ : G →+ ℚ) (x : G)
    (i j k : ℕ) : ℚ :=
  φ (((T - 1) ^ i) (((U - 1) ^ j) (((V - 1) ^ k) x)))

theorem triple_newton_full (T U V : AddMonoid.End G) (φ : G →+ ℚ) (x : G)
    (a b c : ℕ) :
    φ ((T ^ a) ((U ^ b) ((V ^ c) x))) =
      ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        ∑ k ∈ Finset.range (c + 1),
          (a.choose i : ℚ) * (b.choose j : ℚ) * (c.choose k : ℚ) * coefficient T U V φ x i j k := by
  rw [orbit_newton T φ ((U ^ b) ((V ^ c) x)) a]
  apply Finset.sum_congr rfl
  intro i _
  have hU := orbit_newton U (φ.comp (show AddMonoid.End G from (T - 1) ^ i)) ((V ^ c) x) b
  change φ (((T - 1) ^ i) ((U ^ b) ((V ^ c) x))) = _ at hU
  rw [hU, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hV := orbit_newton V
    ((φ.comp (show AddMonoid.End G from (T - 1) ^ i)).comp
      (show AddMonoid.End G from (U - 1) ^ j)) x c
  change φ (((T - 1) ^ i) (((U - 1) ^ j) ((V ^ c) x))) = _ at hV
  change (a.choose i : ℚ) * ((b.choose j : ℚ) *
    φ (((T - 1) ^ i) (((U - 1) ^ j) ((V ^ c) x)))) = _
  rw [hV, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  change (a.choose i : ℚ) * ((b.choose j : ℚ) * ((c.choose k : ℚ) *
    φ (((T - 1) ^ i) (((U - 1) ^ j) (((V - 1) ^ k) x))))) =
    (a.choose i : ℚ) * (b.choose j : ℚ) * (c.choose k : ℚ) *
      φ (((T - 1) ^ i) (((U - 1) ^ j) (((V - 1) ^ k) x)))
  ring

theorem triple_newton (T U V : AddMonoid.End G) (φ : G →+ ℚ) (x : G) (d : ℕ)
    (hzero : ∀ i j k : ℕ, d < i + j + k →
      ((T - 1) ^ i) (((U - 1) ^ j) (((V - 1) ^ k) x)) = 0)
    (a b c : ℕ) :
    φ ((T ^ a) ((U ^ b) ((V ^ c) x))) =
      ∑ i ∈ Finset.range (d + 1), ∑ j ∈ Finset.range (d + 1),
        ∑ k ∈ Finset.range (d + 1),
          (a.choose i : ℚ) * (b.choose j : ℚ) * (c.choose k : ℚ) * coefficient T U V φ x i j k := by
  have hz (i j k : ℕ) (h : d < i + j + k) : coefficient T U V φ x i j k = 0 := by
    rw [coefficient, hzero i j k h, map_zero]
  rw [triple_newton_full]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [choose_sum_truncate a (d + 1) _ (by
    intro i hi
    apply Finset.sum_eq_zero
    intro j _
    rw [Finset.sum_eq_zero (fun k _ => by rw [hz i j k (by omega), mul_zero]), mul_zero])]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [choose_sum_truncate b (d + 1) _ (by
    intro j hj
    apply Finset.sum_eq_zero
    intro k _
    rw [hz i j k (by omega), mul_zero])]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact choose_sum_truncate c (d + 1) _ (fun k hk => hz i j k (by omega))

end OAI.NumberTheory.PadicHodge.IntegralComparison.MixedOrbitNewton
