import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EndomorphismOrbitPolynomial

/-! # Commuting Difference Annihilation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CommutingDifferenceAnnihilation

noncomputable section

/-! Commuting finite differences which annihilate one vector combine without assuming global nilpotence. -/
universe u

theorem endomorphism_pow_apply_zero_of_le {G : Type u} [AddCommGroup G]
    (T : AddMonoid.End G) (v : G) {r n : ℕ} (hr : (T ^ r) v = 0) (hn : r ≤ n) :
    (T ^ n) v = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm r d, pow_add]
  change (T ^ d) ((T ^ r) v) = 0
  rw [hr, map_zero]

theorem commuting_endomorphism_sum_annihilates {G : Type u} [AddCommGroup G]
    (A B : AddMonoid.End G) (hAB : Commute A B) (v : G) (r s : ℕ)
    (hA : (A ^ r) v = 0) (hB : (B ^ s) v = 0) :
    ((A + B) ^ (r + s)) v = 0 := by
  let ψ : AddMonoid.End G →+ G :=
    { toFun := fun T => T v, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hψ (T : AddMonoid.End G) : ψ T = T v := rfl
  calc
    _ = ψ ((A + B) ^ (r + s)) := rfl
    _ = ∑ ij ∈ Finset.antidiagonal (r + s),
        ψ ((r + s).choose ij.1 • (A ^ ij.1 * B ^ ij.2)) := by
      rw [hAB.add_pow', map_sum]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro ij hij
      have hsum := Finset.mem_antidiagonal.mp hij
      have hz : (A ^ ij.1 * B ^ ij.2) v = 0 := by
        by_cases hi : r ≤ ij.1
        · rw [(hAB.pow_pow ij.1 ij.2).eq]
          change (B ^ ij.2) ((A ^ ij.1) v) = 0
          rw [endomorphism_pow_apply_zero_of_le A v hA hi, map_zero]
        · have hj : s ≤ ij.2 := by omega
          change (A ^ ij.1) ((B ^ ij.2) v) = 0
          rw [endomorphism_pow_apply_zero_of_le B v hB hj, map_zero]
      rw [map_nsmul, hψ, hz, nsmul_zero]

theorem commuting_tensor_differences_annihilate {G : Type u} [AddCommGroup G]
    (T U : AddMonoid.End G) (hTU : Commute T U) (v : G) (r s : ℕ)
    (hTUv : ((T * U - 1) ^ r) v = 0) (hUv : ((U - 1) ^ s) v = 0) :
    ((T - 1) ^ (r + s)) v = 0 := by
  let A := T * U - 1
  let B := T * (U - 1)
  have hTB : Commute T (U - 1) := hTU.sub_right (Commute.one_right T)
  have hTA : Commute T A :=
    ((Commute.refl T).mul_right hTU).sub_right (Commute.one_right T)
  have hUA : Commute U A :=
    (hTU.symm.mul_right (Commute.refl U)).sub_right (Commute.one_right U)
  have hAB : Commute A B :=
    hTA.symm.mul_right (hUA.symm.sub_right (Commute.one_right A))
  have hBv : (B ^ s) v = 0 := by
    rw [show B ^ s = T ^ s * (U - 1) ^ s from hTB.mul_pow s]
    change (T ^ s) (((U - 1) ^ s) v) = 0
    rw [hUv, map_zero]
  have hnegBv : ((-B) ^ s) v = 0 := by
    rw [neg_pow]
    change ((-1 : AddMonoid.End G) ^ s) ((B ^ s) v) = 0
    rw [hBv, map_zero]
  have h := commuting_endomorphism_sum_annihilates A (-B) hAB.neg_right v r s hTUv hnegBv
  have he : A + -B = T - 1 := by
    dsimp [A, B]
    rw [mul_sub, mul_one, neg_sub, add_comm, sub_add_sub_cancel]
  rwa [he] at h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CommutingDifferenceAnnihilation
