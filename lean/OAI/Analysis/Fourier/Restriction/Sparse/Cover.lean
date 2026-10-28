import OAI.Analysis.Fourier.Restriction.DensityLayers
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- A finite-set version of Tao's sparse covering lemma. There are `N`
layers and `K+1` colors in each layer. The covering radius is `4*r j`,
while equal-colored centers are separated at the freely prescribed next
scale `r (j+1)`. Taking the scales to grow rapidly gives sparse ball families. -/
theorem finite_sparse_cover {X : Type*} [PseudoMetricSpace X] [DecidableEq X]
    (E : Finset X) (K N : ℕ) (hK : 0 < K) (hN : 0 < N) (hcard : E.card ≤ K ^ N)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hstep : ∀ j < N, 2 * r j ≤ r (j + 1)) :
    ∃ T : Fin N → Finset X, ∃ c : Fin N → X → Fin (K + 1),
      (∀ j, T j ⊆ E) ∧
      (∀ j, ∀ z ∈ T j, ∀ w ∈ T j, z ≠ w → c j z = c j w → r (j + 1) ≤ dist z w) ∧
      ∀ x ∈ E, ∃ j : Fin N, ∃ y ∈ T j, dist x y < 4 * r j := by
  classical
  let A (j : Fin N) : Finset X := E.filter (fun x ↦
    K ^ (j : ℕ) ≤ (E.filter (fun y ↦ dist x y < 2 * r j)).card ∧
    (E.filter (fun y ↦ dist x y < 2 * r (j + 1))).card ≤ K ^ ((j : ℕ) + 1))
  have hex (j : Fin N) : ∃ T : Finset X, ∃ c : X → Fin (K + 1),
      T ⊆ E ∧
      (∀ z ∈ T, ∀ w ∈ T, z ≠ w → c z = c w → r (j + 1) ≤ dist z w) ∧
      ∀ x ∈ A j, ∃ y ∈ T, dist x y < 4 * r j := by
    obtain ⟨T, hTA, hsep, hcover⟩ := finite_separated_cover (A j)
      (show 0 < 4 * r j from mul_pos (by norm_num) (hr j))
    have hTE : T ⊆ E := hTA.trans (Finset.filter_subset _ _)
    have hsmall : ∀ z ∈ T, K ^ (j : ℕ) ≤
        (E.filter (fun y ↦ dist z y < 2 * r j)).card := by
      intro z hz
      exact (Finset.mem_filter.mp (hTA hz)).2.1
    have hlarge : ∀ z ∈ T, (E.filter (fun y ↦ dist z y < 2 * r (j + 1))).card <
        (K + 1) * K ^ (j : ℕ) := by
      intro z hz
      have H := (Finset.mem_filter.mp (hTA hz)).2.2
      have hpow : 0 < K ^ (j : ℕ) := pow_pos hK _
      rw [pow_succ] at H
      nlinarith
    obtain ⟨c, hc⟩ := separated_density_coloring T E (hstep j j.isLt)
      (K ^ (j : ℕ)) (K + 1) (pow_pos hK _) (by omega)
      (by intro z hz w hw hzw; simpa only [show 2 * (2 * r j) = 4 * r j by ring] using hsep z hz w hw hzw)
      hsmall hlarge
    exact ⟨T, c, hTE, hc, hcover⟩
  choose T c hTE hc hcover using hex
  refine ⟨T, c, hTE, hc, ?_⟩
  intro x hx
  obtain ⟨j, hj, hlo, hhi⟩ := exists_density_layer E K N hN hcard r (hr 0) x hx
  let j' : Fin N := ⟨j, hj⟩
  have hxA : x ∈ A j' := Finset.mem_filter.mpr ⟨hx, hlo, hhi⟩
  obtain ⟨y, hy, hxy⟩ := hcover j' x hxA
  exact ⟨j', y, hy, hxy⟩

end OAI.Analysis.Fourier.Restriction
