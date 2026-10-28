import OAI.AlgebraicGeometry.SheafCohomology.Projective.FilteredAlgebraLowerGrowth
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FilteredAlgebraUpperGrowth
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialGrowthDegree

/-! # Filtered Hilbert Dimension -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FilteredHilbertDimension.Dimension

noncomputable section

/-! The eventual dimension polynomial of a finitely generated algebra's degree filtration
has degree equal to its actual Krull dimension. -/

open _root_.MvPolynomial

universe u

theorem polynomialFilteredPiece_Hilbert_leadingCoeff_pos
    (K B : Type u) [Field K] [CommRing B] [Nontrivial B] [Algebra K B]
    {σ : Type*} [Fintype σ] (v : σ → B) (P : Polynomial ℚ) (b : ℕ)
    (hP : ∀ n : ℕ, b ≤ n →
      (Module.finrank K (PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v n) : ℚ) = P.eval (n : ℚ)) :
    0 < P.leadingCoeff := by
  have h₁ : (1 : B) ∈ PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v b := by
    simpa using PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece_algebraMap v b (1 : K)
  have : Nontrivial (PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v b) :=
    ⟨⟨⟨1, h₁⟩, 0, fun h => one_ne_zero (congrArg Subtype.val h)⟩⟩
  have hpos : 0 < Module.finrank K (PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v b) := Module.finrank_pos
  have hp0 : P ≠ 0 := by
    intro hz
    have he := hP b le_rfl
    rw [hz, Polynomial.eval_zero] at he
    exact hpos.ne' (Nat.cast_eq_zero.mp he)
  exact lt_of_le_of_ne
    (PolynomialGrowthDegree.Dimension.polynomial_leadingCoeff_nonneg_of_eventually_nat_eval_nonneg P b
      (fun n hn => (hP n hn) ▸ Nat.cast_nonneg _))
    (Polynomial.leadingCoeff_ne_zero.mpr hp0).symm

theorem polynomialFilteredPiece_Hilbert_natDegree
    (K B : Type u) [Field K] [CommRing B] [Nontrivial B]
    [Algebra K B] [Algebra.FiniteType K B]
    {σ : Type*} [Fintype σ] (v : σ → B) (hv : Algebra.adjoin K (Set.range v) = ⊤)
    (P : Polynomial ℚ) (b : ℕ)
    (hP : ∀ n : ℕ, b ≤ n →
      (Module.finrank K (PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v n) : ℚ) = P.eval (n : ℚ)) :
    (P.natDegree : WithBot ℕ∞) = ringKrullDim B := by
  obtain ⟨g, φ, hφ, hfin, hdim⟩ := NoetherNormalizationDimension.Dimension.noetherNormalization_krullDimension K B
  obtain ⟨c₁, hc₁, hlo⟩ := FilteredAlgebraLowerGrowth.Dimension.polynomialFilteredPiece_independent_lower_bound v hv g φ hφ
  obtain ⟨c₂, D, hc₂, hhi⟩ := FilteredAlgebraUpperGrowth.Dimension.polynomialFilteredPiece_upper_growth_of_finite φ hfin v
  have hlc := polynomialFilteredPiece_Hilbert_leadingCoeff_pos K B v P b hP
  have hd : P.natDegree = g := by
    apply PolynomialGrowthDegree.Dimension.polynomial_natDegree_eq_of_power_growth P hlc g b c₁ c₂ D hc₁ hc₂
    · intro n hn
      have he := hP (n * c₁) (hn.trans (Nat.le_mul_of_pos_right n hc₁))
      rw [Nat.cast_mul] at he
      rw [← he]
      exact_mod_cast hlo n
    · intro n hn
      rw [← hP n hn]
      have hb := hhi n
      rw [Fintype.card_fin] at hb
      exact_mod_cast hb
  rw [hd]
  exact hdim.symm

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FilteredHilbertDimension.Dimension
