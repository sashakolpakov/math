import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Group.Units.Basic

/-! # Auxiliary Level Frame Bounds -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AuxiliaryLevelFrameBounds

noncomputable section

/-! Raising the original level to a power produces an explicit level
larger than any prescribed frame threshold and introduces no new primes.
The resulting arithmetic converts a degree bound on hyperplane torsion
counts into the strict sparsity inequality. -/

def frameAuxiliaryLevel (N r D : ℕ) : ℕ := N ^ (r * D + 1)

theorem threshold_lt_power (N : ℕ) (hN : 2 ≤ N) (a : ℕ) : a < N ^ (a + 1) := by
  induction a with
  | zero => simpa only [Nat.zero_add, pow_one] using (Nat.lt_of_lt_of_le (by decide : 0 < 2) hN)
  | succ a ih =>
      calc
        a + 1 < 2 * (a + 1) := by omega
        _ ≤ N * N ^ (a + 1) := Nat.mul_le_mul hN (Nat.succ_le_of_lt ih)
        _ = N ^ (a + 1 + 1) := (Nat.mul_comm _ _).trans (pow_succ N (a + 1)).symm

theorem frameAuxiliaryLevel_multiple (N r D : ℕ) : N ∣ frameAuxiliaryLevel N r D := by
  refine ⟨N ^ (r * D), ?_⟩
  exact (pow_succ N (r * D)).trans (Nat.mul_comm _ _)

theorem frameAuxiliaryLevel_square_gt (N r D : ℕ) (hN : 2 ≤ N) :
    r * D < (frameAuxiliaryLevel N r D) ^ 2 := by
  have h := threshold_lt_power N hN (r * D)
  change r * D < frameAuxiliaryLevel N r D at h
  have hp : 0 < frameAuxiliaryLevel N r D := Nat.lt_of_le_of_lt (Nat.zero_le _) h
  have hm : frameAuxiliaryLevel N r D ≤ frameAuxiliaryLevel N r D * frameAuxiliaryLevel N r D := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (frameAuxiliaryLevel N r D) (Nat.succ_le_of_lt hp)
  exact h.trans_le (by simpa only [pow_two] using hm)

theorem frameAuxiliaryLevel_unit {R : Type*} [CommRing R] (N r D : ℕ)
    (hN : IsUnit (N : R)) : IsUnit (frameAuxiliaryLevel N r D : R) := by
  change IsUnit ((N ^ (r * D + 1) : ℕ) : R)
  rw [Nat.cast_pow]
  exact hN.pow _

theorem torsionCount_sparse_of_degree_bound (g r D L c : ℕ)
    (hg : 0 < g) (hL : 0 < L) (hlarge : r * D < L ^ 2)
    (hcount : c ≤ D * L ^ (2 * g - 2)) : r * c < L ^ (2 * g) := by
  calc
    r * c ≤ r * (D * L ^ (2 * g - 2)) := Nat.mul_le_mul_left r hcount
    _ = (r * D) * L ^ (2 * g - 2) := (Nat.mul_assoc _ _ _).symm
    _ < L ^ 2 * L ^ (2 * g - 2) := Nat.mul_lt_mul_of_pos_right hlarge (Nat.pow_pos hL)
    _ = L ^ (2 * g) := by
      rw [← pow_add]
      congr 1
      omega

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AuxiliaryLevelFrameBounds
