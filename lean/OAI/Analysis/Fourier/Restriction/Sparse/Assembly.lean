import OAI.Analysis.Fourier.Restriction.FiniteCover
import OAI.Analysis.Fourier.Restriction.BallCover

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- The sparse-ball estimate used in epsilon removal. The separation depends
polynomially on both radius and the actual number of centers. -/
def SparseFourierBound (n : ℕ) (p : ℝ≥0∞) (α : ℝ) (D : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ R : ℝ, 1 ≤ R → ∀ T : Finset (Space n),
    (∀ z ∈ T, ∀ w ∈ T, z ≠ w → R ^ D * (T.card : ℝ) ^ D ≤ dist z w) →
    ∀ f : Space n → ℂ, Measurable f → Integrable f →
      (∀ x, (∀ z ∈ T, x ∉ ball z R) → f x = 0) →
        eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) p (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
          C * ENNReal.ofReal (R ^ α) * eLpNorm f p volume

/-- Sparse estimates and the quantitative geometric cover give an explicit
norm bound on every finite union of unit balls. -/
theorem sparseFourierBound_unit_ball_cover {n : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {α : ℝ} (hα : 0 ≤ α) {D : ℕ} (hD : 0 < D) {C : ℝ≥0∞}
    (hSparse : SparseFourierBound n p α D C)
    (E : Finset (Space n)) (M N : ℕ) (hM : 1 ≤ M) (hcard : E.card ≤ M) (hN : 0 < N)
    {f : Space n → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (hfs : ∀ x, (∀ e ∈ E, x ∉ ball e 1) → f x = 0) :
    eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) p (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      ENNReal.ofReal (3 * N * (M : ℝ) ^ (1 / (N : ℝ))) *
        (C * ENNReal.ofReal ((5 * (4 * ((M : ℝ) + 1)) ^ ((3 * D + 1) ^ N)) ^ α)) *
          eLpNorm f p volume := by
  classical
  obtain ⟨K, T, c, hcount, hTE, hsep, hcover, hR⟩ :=
    unit_ball_sparse_cover E M N D hM hcard hN hD
  let S (i : Fin N × Fin (K + 1)) := (T i.1).filter (fun z ↦ c i.1 z = i.2)
  let R (j : Fin N) := 5 * sparseScale M D j
  let Rmax : ℝ := 5 * (4 * ((M : ℝ) + 1)) ^ ((3 * D + 1) ^ N)
  let U (i : Fin N × Fin (K + 1)) := ⋃ z ∈ S i, ball z (R i.1)
  have hUm : ∀ i, MeasurableSet (U i) := by
    intro i
    exact (isOpen_iUnion fun z ↦ isOpen_iUnion fun _ ↦ isOpen_ball).measurableSet
  have hRi (j : Fin N) : 1 ≤ R j := by
    have H := sparseScale_ge_four M D j
    dsimp [R]
    linarith
  have hSi (i : Fin N × Fin (K + 1)) : (S i).card ≤ M :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans
      ((Finset.card_le_card (hTE i.1)).trans hcard)
  have hSsep (i : Fin N × Fin (K + 1)) : ∀ z ∈ S i, ∀ w ∈ S i,
      z ≠ w → (R i.1) ^ D * ((S i).card : ℝ) ^ D ≤ dist z w := by
    intro z hz w hw hzw
    have hz' := Finset.mem_filter.mp hz
    have hw' := Finset.mem_filter.mp hw
    have H := hsep i.1 z hz'.1 w hw'.1 hzw (hz'.2.trans hw'.2.symm)
    apply le_trans _ H
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (le_trans zero_le_one (hRi i.1)) D)
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hSi i) D
  have H := fourier_bound_of_finite_cover Finset.univ U hUm
    (fun i ↦ C * ENNReal.ofReal ((R i.1) ^ α)) hp (fun i _ g hgm hgi hgs ↦ by
      apply hSparse (R i.1) (hRi i.1) (S i) (hSsep i) g hgm hgi
      intro x hx
      apply hgs x
      simp only [U, mem_iUnion, not_exists]
      exact hx) hf hfi (fun x hx ↦ by
        apply hfs x
        intro e he hxe
        obtain ⟨j, y, hy, hxy⟩ := hcover x ⟨e, he, hxe⟩
        apply hx (j, c j y) (Finset.mem_univ _)
        change x ∈ ⋃ z ∈ S (j, c j y), ball z (R j)
        exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hy, rfl⟩, hxy⟩⟩)
  have hsum : (∑ i : Fin N × Fin (K + 1), C * ENNReal.ofReal ((R i.1) ^ α)) ≤
      ((N * (K + 1) : ℕ) : ℝ≥0∞) * (C * ENNReal.ofReal (Rmax ^ α)) := by
    calc
      _ ≤ ∑ _i : Fin N × Fin (K + 1), C * ENNReal.ofReal (Rmax ^ α) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul le_rfl _ zero_le zero_le
        apply ENNReal.ofReal_le_ofReal
        exact Real.rpow_le_rpow (le_trans zero_le_one (hRi i.1)) (hR i.1) hα
      _ = _ := by simp [Fintype.card_prod, nsmul_eq_mul]
  have hcountE : ((N * (K + 1) : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (3 * N * (M : ℝ) ^ (1 / (N : ℝ))) := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcount
  exact H.trans (mul_le_mul (hsum.trans (mul_le_mul hcountE le_rfl zero_le zero_le)) le_rfl zero_le zero_le)

end OAI.Analysis.Fourier.Restriction
