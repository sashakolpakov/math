import OAI.NumberTheory.ArithmeticGroups.Lattices.AveragedGramMatrix

/-! # Invariant Gram -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.InvariantGram.Construction

noncomputable section

/-! Haar averaging gives an invariant positive quadratic form for a
compact real matrix group. -/

open scoped Classical _root_.Matrix.Norms.Elementwise
open _root_.MeasureTheory _root_.MeasureTheory.Measure _root_.Matrix

local instance congruenceMatrixContinuousENorm (n : ℕ) : ContinuousENorm (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (ContinuousENorm (Fin n → Fin n → ℝ))

theorem inverseGram_congruence
    {H : Type} [Group H] {n : ℕ} (ρ : H →* Algebraic.SL n ℝ) (h g : H) :
    AveragedGramMatrix.Construction.matrixCongruence (ρ h : Matrix (Fin n) (Fin n) ℝ) (AveragedGramMatrix.Construction.inverseGram ρ g) =
      AveragedGramMatrix.Construction.inverseGram ρ (h⁻¹ * g) := by
  simp [AveragedGramMatrix.Construction.matrixCongruence, AveragedGramMatrix.Construction.inverseGram, _root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.transpose_mul, Matrix.mul_assoc]

theorem averagedGram_invariant
    {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [MeasurableSpace H] [BorelSpace H] {n : ℕ}
    (ρ : H →* Algebraic.SL n ℝ) (hρ : Continuous ρ) (μ : Measure H)
    [IsFiniteMeasureOnCompacts μ] [IsMulLeftInvariant μ] (h : H) :
    (ρ h : Matrix (Fin n) (Fin n) ℝ).transpose * AveragedGramMatrix.Construction.averagedGram ρ μ *
      (ρ h : Matrix (Fin n) (Fin n) ℝ) = AveragedGramMatrix.Construction.averagedGram ρ μ := by
  let L := (AveragedGramMatrix.Construction.matrixCongruence (ρ h : Matrix (Fin n) (Fin n) ℝ)).toContinuousLinearMap
  have he := L.integral_comp_comm (μ := μ) (φ := AveragedGramMatrix.Construction.inverseGram ρ) (AveragedGramMatrix.Construction.inverseGram_integrable ρ hρ μ)
  change L (∫ g, AveragedGramMatrix.Construction.inverseGram ρ g ∂μ) = ∫ g, AveragedGramMatrix.Construction.inverseGram ρ g ∂μ
  have he' : L (∫ g, AveragedGramMatrix.Construction.inverseGram ρ g ∂μ) = ∫ g, L (AveragedGramMatrix.Construction.inverseGram ρ g) ∂μ := by
    convert! he.symm
  rw [he']
  have hi (g : H) : L (AveragedGramMatrix.Construction.inverseGram ρ g) = AveragedGramMatrix.Construction.inverseGram ρ (h⁻¹ * g) := inverseGram_congruence ρ h g
  simp_rw [hi]
  exact integral_mul_left_eq_self (AveragedGramMatrix.Construction.inverseGram ρ) h⁻¹

theorem exists_compact_invariant_positive_matrix
    {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [MeasurableSpace H] [BorelSpace H] {n : ℕ}
    (ρ : H →* Algebraic.SL n ℝ) (hρ : Continuous ρ) (μ : Measure H)
    [IsFiniteMeasureOnCompacts μ] [IsMulLeftInvariant μ] [IsOpenPosMeasure μ] :
    ∃ Q : Matrix (Fin n) (Fin n) ℝ,
      (∀ x : Fin n → ℝ, x ≠ 0 → 0 < dotProduct x (Q.mulVec x)) ∧
      ∀ g, (ρ g : Matrix (Fin n) (Fin n) ℝ).transpose * Q *
        (ρ g : Matrix (Fin n) (Fin n) ℝ) = Q :=
  ⟨AveragedGramMatrix.Construction.averagedGram ρ μ, fun _ hx => AveragedGramMatrix.Construction.averagedGram_quadratic_pos ρ hρ μ hx, averagedGram_invariant ρ hρ μ⟩

theorem exists_invariant_positive_matrix_of_compact
    {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [T2Space H] {n : ℕ} (ρ : H →* Algebraic.SL n ℝ) (hρ : Continuous ρ) :
    ∃ Q : Matrix (Fin n) (Fin n) ℝ,
      (∀ x : Fin n → ℝ, x ≠ 0 → 0 < dotProduct x (Q.mulVec x)) ∧
      ∀ g, (ρ g : Matrix (Fin n) (Fin n) ℝ).transpose * Q *
        (ρ g : Matrix (Fin n) (Fin n) ℝ) = Q := by
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  exact exists_compact_invariant_positive_matrix ρ hρ (haar (G := H))

theorem compact_real_place_invariant_positive_matrix
    {k : Type} [Field k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (v : k →+* ℝ) (hv : Algebraic.IsCompactAtRealPlace G v) :
    ∃ Q : Matrix (Fin G.dimension) (Fin G.dimension) ℝ,
      (∀ x : Fin G.dimension → ℝ, x ≠ 0 → 0 < dotProduct x (Q.mulVec x)) ∧
      ∀ g : G.matrixGroup.Points v,
        (g.val : Matrix (Fin G.dimension) (Fin G.dimension) ℝ).transpose * Q *
          (g.val : Matrix (Fin G.dimension) (Fin G.dimension) ℝ) = Q := by
  let : CompactSpace (G.matrixGroup.Points v) := hv
  exact exists_invariant_positive_matrix_of_compact
    (G.matrixGroup.subgroup ℝ v).subtype continuous_subtype_val

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.InvariantGram.Construction
