import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Existence

/-! # Twist Rank Rigidity -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.TwistRankRigidity

/-! In positive projective dimension, the nonnegative twist section
rank is strictly increasing; rank n+1 uniquely identifies degree one. -/

theorem projectiveTwistRank_strictMono (n : ℕ) (hn : 0 < n) :
    StrictMono (fun d : ℕ => (d + n).choose n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  apply strictMono_nat_of_lt_succ
  intro d
  have hp : 0 < (d + (k + 1)).choose k := Nat.choose_pos (by omega)
  change (d + (k + 1)).choose (k + 1) < (d + 1 + (k + 1)).choose (k + 1)
  rw [show d + 1 + (k + 1) = (d + (k + 1)) + 1 by omega, Nat.choose_succ_succ']
  omega

theorem projectiveTwistRank_eq_dimension_iff (n : ℕ) (hn : 0 < n) (d : ℕ) :
    (d + n).choose n = n + 1 ↔ d = 1 := by
  have h1 : (1 + n).choose n = n + 1 := by
    rw [Nat.add_comm, Nat.choose_succ_self_right]
  rw [← h1]
  exact (projectiveTwistRank_strictMono n hn).injective.eq_iff

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.TwistRankRigidity
