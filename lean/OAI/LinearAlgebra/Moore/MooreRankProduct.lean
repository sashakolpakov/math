import Mathlib.Analysis.Matrix.PosDef

noncomputable section
open scoped BigOperators
namespace OAI.LinearAlgebra.Moore

theorem rank_power_bound {N k r : ℕ} {M a : ℝ}
    (hkr : k ≤ r) (hrN : r ≤ N) (hM : 0 ≤ M) (ha : 0 ≤ a) :
    (M + a) ^ k * a ^ (N - k) ≤ (M + a) ^ r * a ^ (N - r) := by
  have hNk : N - k = (r - k) + (N - r) := by omega
  have hr : r = k + (r - k) := by omega
  have hp : a ^ (r - k) ≤ (M + a) ^ (r - k) :=
    pow_le_pow_left₀ ha (by linarith) _
  calc
    _ = (M + a) ^ k * a ^ (r - k) * a ^ (N - r) := by
      rw [hNk, pow_add, mul_assoc]
    _ ≤ (M + a) ^ k * (M + a) ^ (r - k) * a ^ (N - r) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (pow_nonneg (add_nonneg hM ha) k))
        (pow_nonneg ha _)
    _ = _ := by rw [← pow_add, ← hr]

theorem product_shift_le_of_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) {M a : ℝ} {r : ℕ}
    (hv : ∀ i, 0 ≤ v i) (hM : 0 ≤ M) (hbound : ∀ i, v i ≤ M)
    (ha : 0 ≤ a) (hr : Fintype.card {i // v i ≠ 0} ≤ r)
    (hrN : r ≤ Fintype.card ι) :
    (∏ i, (v i + a)) ≤ (M + a) ^ r * a ^ (Fintype.card ι - r) := by
  classical
  let s : Finset ι := Finset.univ.filter (fun i => v i ≠ 0)
  have hs : s.card = Fintype.card {i // v i ≠ 0} := by
    simp [s, Fintype.card_subtype]
  have hprod : (∏ i, (v i + a)) = (∏ i ∈ s, (v i + a)) * a ^ (Fintype.card ι - s.card) := by
    rw [← Finset.prod_sdiff (Finset.subset_univ s)]
    have hz : (∏ i ∈ Finset.univ \ s, (v i + a)) = a ^ (Fintype.card ι - s.card) := by
      have hc : (Finset.univ \ s).card = Fintype.card ι - s.card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ s), Finset.card_univ]
      rw [← hc, ← Finset.prod_const]
      apply Finset.prod_congr rfl
      intro i hi
      have : v i = 0 := by simpa [s] using (Finset.mem_sdiff.mp hi).2
      simp [this]
    rw [hz, mul_comm]
  rw [hprod]
  calc
    _ ≤ (M + a) ^ s.card * a ^ (Fintype.card ι - s.card) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg ha _)
      rw [← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun i _ => add_nonneg (hv i) ha)
        (fun i _ => add_le_add (hbound i) le_rfl)
    _ ≤ _ := rank_power_bound (by simpa [hs] using hr) hrN hM ha

end OAI.LinearAlgebra.Moore
