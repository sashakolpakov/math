import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.CountSelection
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Weighted Veronese Extraction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.WeightedVeroneseExtraction

noncomputable section

/-! An explicit Veronese degree: with n positive weights dividing L,
every exponent vector of positive degree divisible by nL contains a
subvector of degree nL. Remainders consume fewer than n whole L-blocks. -/
open scoped BigOperators Classical

def weightedExponentDegree {n : ℕ} (w a : Fin n → ℕ) : ℕ := ∑ i, a i * w i

theorem weightedVeronese_exists_subexponent {n : ℕ} (hn : 0 < n)
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) (L : ℕ) (hL : 0 < L)
    (hwL : ∀ i, w i ∣ L) (a : Fin n → ℕ) (k : ℕ) (hk : 0 < k)
    (ha : weightedExponentDegree w a = k * (n * L)) :
    ∃ b : Fin n → ℕ, (∀ i, b i ≤ a i) ∧ weightedExponentDegree w b = n * L := by
  let q : Fin n → ℕ := fun i => L / w i
  let rem : Fin n → ℕ := fun i => a i % q i
  let quot : Fin n → ℕ := fun i => a i / q i
  have hq (i : Fin n) : q i * w i = L := Nat.div_mul_cancel (hwL i)
  have hqpos (i : Fin n) : 0 < q i := Nat.div_pos (Nat.le_of_dvd hL (hwL i)) (hw i)
  have hrem (i : Fin n) : rem i * w i < L := by
    rw [← hq i]
    exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (hqpos i)) (hw i)
  have hsplit (b : Fin n → ℕ) :
      weightedExponentDegree w (fun i => rem i + q i * b i) =
        weightedExponentDegree w rem + L * ∑ i, b i := by
    unfold weightedExponentDegree
    simp_rw [add_mul, show ∀ i, q i * b i * w i = L * b i from fun i => by
      rw [Nat.mul_right_comm, hq i]]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  have haSplit : weightedExponentDegree w a = weightedExponentDegree w rem + L * ∑ i, quot i := by
    rw [← hsplit quot]
    congr 1
    funext i
    exact (Nat.mod_add_div (a i) (q i)).symm
  have hremLt : weightedExponentDegree w rem < n * L := by
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    simpa only [weightedExponentDegree, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using
      Finset.sum_lt_sum_of_nonempty hne (fun i _ => hrem i)
  have hdtotal : L ∣ weightedExponentDegree w a := by
    rw [ha]
    exact ⟨k * n, by ring⟩
  have hdrem : L ∣ weightedExponentDegree w rem := by
    have hh := Nat.dvd_sub hdtotal (dvd_mul_right L (∑ i, quot i))
    rw [haSplit, Nat.add_sub_cancel_right] at hh
    exact hh
  obtain ⟨c, hc⟩ := hdrem
  have hcn : c < n := by nlinarith
  have hsum : c + ∑ i, quot i = k * n := by
    apply Nat.eq_of_mul_eq_mul_left hL
    calc
      L * (c + ∑ i, quot i) = weightedExponentDegree w a := by rw [haSplit, hc]; ring
      _ = L * (k * n) := by rw [ha]; ring
  have hnk : n ≤ k * n := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right n (Nat.succ_le_of_lt hk)
  have hcap : n - c ≤ ∑ i, quot i := by omega
  obtain ⟨b, hb, hbSum⟩ := Bounded.CountSelection.exists_bounded_counts_with_sum quot (n - c) hcap
  refine ⟨fun i => rem i + q i * b i, ?_, ?_⟩
  · intro i
    calc
      rem i + q i * b i ≤ rem i + q i * quot i := Nat.add_le_add_left (Nat.mul_le_mul_left _ (hb i)) _
      _ = a i := Nat.mod_add_div (a i) (q i)
  · rw [hsplit, hc, hbSum, ← Nat.mul_add, Nat.add_sub_of_le hcn.le, Nat.mul_comm]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.WeightedVeroneseExtraction
