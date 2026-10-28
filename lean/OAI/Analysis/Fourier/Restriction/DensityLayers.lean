import OAI.Analysis.Fourier.Restriction.Sparse.Counting
import Mathlib.Data.Nat.Find

noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- Every point has a first density scale. This elementary stopping-time
step is the source of the small number of sparse families in epsilon removal. -/
theorem exists_density_layer {X : Type*} [PseudoMetricSpace X] [DecidableEq X]
    (E : Finset X) (K N : ℕ) (hN : 0 < N) (hcard : E.card ≤ K ^ N)
    (r : ℕ → ℝ) (hr0 : 0 < r 0) (x : X) (hx : x ∈ E) :
    ∃ j < N,
      K ^ j ≤ (E.filter (fun y ↦ dist x y < 2 * r j)).card ∧
      (E.filter (fun y ↦ dist x y < 2 * r (j + 1))).card ≤ K ^ (j + 1) := by
  classical
  let P (k : ℕ) : Prop := 0 < k ∧ k ≤ N ∧
    (E.filter (fun y ↦ dist x y < 2 * r k)).card ≤ K ^ k
  have hex : ∃ k, P k := ⟨N, hN, le_rfl, (Finset.card_filter_le _ _).trans hcard⟩
  let k := Nat.find hex
  have hk : P k := Nat.find_spec hex
  have hkpos : 0 < k := hk.1
  have hkle : k ≤ N := hk.2.1
  have hnext : k - 1 + 1 = k := by omega
  refine ⟨k - 1, by omega, ?_, ?_⟩
  · by_cases hkone : k = 1
    · have hcount : 0 < (E.filter (fun y ↦ dist x y < 2 * r 0)).card := by
        apply Finset.card_pos.mpr
        exact ⟨x, Finset.mem_filter.mpr ⟨hx, by simpa using (mul_pos (by norm_num : (0 : ℝ) < 2) hr0)⟩⟩
      convert Nat.succ_le_of_lt hcount using 1 <;> simp [hkone]
    · have hnot : ¬ P (k - 1) := Nat.find_min hex (by omega)
      have hkminus : 0 < k - 1 := by omega
      have hkminusN : k - 1 ≤ N := by omega
      have hlarge : K ^ (k - 1) < (E.filter (fun y ↦ dist x y < 2 * r (k - 1))).card := by
        by_contra! h
        exact hnot ⟨hkminus, hkminusN, h⟩
      exact hlarge.le
  · simpa only [hnext] using hk.2.2

end OAI.Analysis.Fourier.Restriction
