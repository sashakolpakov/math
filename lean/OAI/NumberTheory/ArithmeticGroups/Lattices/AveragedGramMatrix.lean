import OAI.NumberTheory.ArithmeticGroups.Lattices.Realizations

/-! # Averaged Gram Matrix -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.AveragedGramMatrix.Construction

noncomputable section

section

/-! Averaging Gram matrices over a compact real matrix group. The
resulting matrix gives a positive quadratic form. -/

open scoped Classical _root_.Matrix.Norms.Elementwise
open _root_.MeasureTheory _root_.MeasureTheory.Measure _root_.Matrix

local instance matrixContinuousENorm (n : ℕ) : ContinuousENorm (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (ContinuousENorm (Fin n → Fin n → ℝ))

def matrixQuadraticEvaluation {n : ℕ} (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ where
  toFun Q := dotProduct x (Q.mulVec x)
  map_add' Q R := by simp [Matrix.add_mulVec, dotProduct_add]
  map_smul' c Q := by simp [Matrix.smul_mulVec, dotProduct_smul]

def matrixCongruence {n : ℕ} (g : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun Q := g.transpose * Q * g
  map_add' Q R := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c Q := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

def inverseGram {H : Type} [Group H] {n : ℕ} (ρ : H →* Algebraic.SL n ℝ) (g : H) :
    Matrix (Fin n) (Fin n) ℝ :=
  (ρ g⁻¹ : Matrix (Fin n) (Fin n) ℝ).transpose * (ρ g⁻¹ : Matrix (Fin n) (Fin n) ℝ)

def averagedGram {H : Type} [Group H] [MeasurableSpace H] {n : ℕ}
    (ρ : H →* Algebraic.SL n ℝ) (μ : Measure H) : Matrix (Fin n) (Fin n) ℝ := ∫ g, inverseGram ρ g ∂μ

theorem continuous_inverseGram
    {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {n : ℕ}
    (ρ : H →* Algebraic.SL n ℝ) (hρ : Continuous ρ) : Continuous (inverseGram ρ) := by
  have hc : Continuous (fun g : H => (ρ g⁻¹ : Matrix (Fin n) (Fin n) ℝ)) :=
    continuous_subtype_val.comp (hρ.comp continuous_inv)
  exact hc.matrix_transpose.mul hc

theorem inverseGram_integrable
    {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [MeasurableSpace H] [BorelSpace H] {n : ℕ}
    (ρ : H →* Algebraic.SL n ℝ) (hρ : Continuous ρ) (μ : Measure H) [IsFiniteMeasureOnCompacts μ] :
    Integrable (inverseGram ρ) μ := by
  exact (continuous_inverseGram ρ hρ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem inverseGram_quadratic_nonneg
    {H : Type} [Group H] {n : ℕ} (ρ : H →* Algebraic.SL n ℝ) (g : H) (x : Fin n → ℝ) :
    0 ≤ matrixQuadraticEvaluation x (inverseGram ρ g) := by
  change 0 ≤ dotProduct x (((ρ g⁻¹ : Matrix (Fin n) (Fin n) ℝ).transpose *
    (ρ g⁻¹ : Matrix (Fin n) (Fin n) ℝ)).mulVec x)
  have h := (Matrix.posSemidef_conjTranspose_mul_self
    (ρ g⁻¹ : Matrix (Fin n) (Fin n) ℝ)).dotProduct_mulVec_nonneg x
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, star_trivial] using h

theorem inverseGram_quadratic_one_pos
    {H : Type} [Group H] {n : ℕ} (ρ : H →* Algebraic.SL n ℝ) {x : Fin n → ℝ} (hx : x ≠ 0) :
    0 < matrixQuadraticEvaluation x (inverseGram ρ 1) := by
  have he : inverseGram ρ 1 = 1 := by simp [inverseGram]
  rw [he]
  change 0 < dotProduct x ((1 : Matrix (Fin n) (Fin n) ℝ).mulVec x)
  rw [Matrix.one_mulVec]
  simpa only [star_trivial] using (dotProduct_star_self_pos_iff (v := x)).mpr hx

theorem averagedGram_quadratic_pos
    {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [MeasurableSpace H] [BorelSpace H] {n : ℕ}
    (ρ : H →* Algebraic.SL n ℝ) (hρ : Continuous ρ) (μ : Measure H)
    [IsFiniteMeasureOnCompacts μ] [IsOpenPosMeasure μ]
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    0 < matrixQuadraticEvaluation x (averagedGram ρ μ) := by
  let L := (matrixQuadraticEvaluation x).toContinuousLinearMap
  have he := L.integral_comp_comm (μ := μ) (φ := inverseGram ρ) (inverseGram_integrable ρ hρ μ)
  change 0 < L (∫ g, inverseGram ρ g ∂μ)
  have he' : L (∫ g, inverseGram ρ g ∂μ) = ∫ g, L (inverseGram ρ g) ∂μ := by
    convert! he.symm
  rw [he']
  have hc : Continuous (fun g => L (inverseGram ρ g)) := L.continuous.comp (continuous_inverseGram ρ hρ)
  exact hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (HasCompactSupport.of_compactSpace _)
    (fun g => inverseGram_quadratic_nonneg ρ g x) (ne_of_gt (inverseGram_quadratic_one_pos ρ hx))

end

/-! Strict positivity of a real quadratic form is an open condition
on its coefficient matrix, using compactness of the unit sphere. -/

open scoped Classical _root_.Matrix.Norms.Elementwise
open _root_.Matrix Set

theorem matrix_quadratic_smul {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (c : ℝ) (x : Fin n → ℝ) :
    dotProduct (c • x) (Q.mulVec (c • x)) = c ^ 2 * dotProduct x (Q.mulVec x) := by
  simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem matrix_quadratic_positive_iff_sphere {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) :
    (∀ x : Fin n → ℝ, x ≠ 0 → 0 < dotProduct x (Q.mulVec x)) ↔
      ∀ x : Metric.sphere (0 : Fin n → ℝ) 1, 0 < dotProduct x.val (Q.mulVec x.val) := by
  constructor
  · intro h x
    apply h
    intro hx
    have hn := x.property
    simp [hx] at hn
  · intro h x hx
    have hn : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := norm_smul_inv_norm hx
    have hp := h ⟨(‖x‖⁻¹ : ℝ) • x, by simpa only [Metric.mem_sphere, dist_zero_right] using hn⟩
    change 0 < dotProduct ((‖x‖⁻¹ : ℝ) • x) (Q.mulVec ((‖x‖⁻¹ : ℝ) • x)) at hp
    rw [matrix_quadratic_smul] at hp
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos (inv_pos.mpr (norm_pos_iff.mpr hx)))).mp hp

theorem isOpen_positive_quadratic_matrices (n : ℕ) :
    IsOpen {Q : Matrix (Fin n) (Fin n) ℝ |
      ∀ x : Fin n → ℝ, x ≠ 0 → 0 < dotProduct x (Q.mulVec x)} := by
  let S := Metric.sphere (0 : Fin n → ℝ) 1
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Fin n → ℝ) 1)
  have hc : Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × S =>
      dotProduct p.2.val (p.1.mulVec p.2.val)) := by
    simp only [Matrix.mulVec, dotProduct]
    apply continuous_finsetSum
    intro i _
    apply Continuous.mul
    · exact (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
    · apply continuous_finsetSum
      intro j _
      exact ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst)).mul
        ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd))
  have hbad : IsClosed {p : Matrix (Fin n) (Fin n) ℝ × S |
      dotProduct p.2.val (p.1.mulVec p.2.val) ≤ 0} := isClosed_le hc continuous_const
  have hp := (isClosedMap_fst_of_compactSpace (X := Matrix (Fin n) (Fin n) ℝ) (Y := S)) _ hbad
  have he : {Q : Matrix (Fin n) (Fin n) ℝ |
      ∀ x : Fin n → ℝ, x ≠ 0 → 0 < dotProduct x (Q.mulVec x)} =
      (Prod.fst '' {p : Matrix (Fin n) (Fin n) ℝ × S |
        dotProduct p.2.val (p.1.mulVec p.2.val) ≤ 0})ᶜ := by
    ext Q
    simp only [Set.mem_ofPred_eq, matrix_quadratic_positive_iff_sphere, Set.mem_compl_iff,
      Set.mem_image, Prod.exists, exists_and_right, exists_eq_right, not_exists, not_le]
    rfl
  rw [he]
  exact hp.isOpen_compl

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.AveragedGramMatrix.Construction
