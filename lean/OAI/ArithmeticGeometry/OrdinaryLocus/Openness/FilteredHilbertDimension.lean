import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FilteredAlgebraLowerGrowth
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FilteredAlgebraUpperGrowth
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PolynomialGrowthDegree

/-! # Filtered Hilbert Dimension -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FilteredHilbertDimension.Construction

noncomputable section

/-! The eventual dimension polynomial of a finitely generated algebra's degree filtration
has degree equal to its actual Krull dimension. -/

open _root_.MvPolynomial

universe u

theorem polynomialFilteredPiece_Hilbert_natDegree
    (K B : Type u) [Field K] [CommRing B] [Nontrivial B]
    [Algebra K B] [Algebra.FiniteType K B]
    {σ : Type*} [Fintype σ] (v : σ → B) (hv : Algebra.adjoin K (Set.range v) = ⊤)
    (P : Polynomial ℚ) (b : ℕ)
    (hP : ∀ n : ℕ, b ≤ n →
      (Module.finrank K (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) v n) : ℚ) = P.eval (n : ℚ)) :
    (P.natDegree : WithBot ℕ∞) = ringKrullDim B := by
  obtain ⟨g, φ, hφ, hfin, hdim⟩ := NoetherNormalizationDimension.Construction.noetherNormalization_krullDimension K B
  obtain ⟨c₁, hc₁, hlo⟩ := FilteredAlgebraLowerGrowth.Construction.polynomialFilteredPiece_independent_lower_bound v hv g φ hφ
  obtain ⟨c₂, D, hc₂, hhi⟩ := FilteredAlgebraUpperGrowth.Construction.polynomialFilteredPiece_upper_growth_of_finite φ hfin v
  have h₁ : (1 : B) ∈ PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) v b := by
    simpa using PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece_algebraMap v b (1 : K)
  have : Nontrivial (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) v b) :=
    ⟨⟨⟨1, h₁⟩, 0, fun h => one_ne_zero (congrArg Subtype.val h)⟩⟩
  have hpos : 0 < Module.finrank K (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) v b) := Module.finrank_pos
  have hp0 : P ≠ 0 := by
    intro hz
    have he := hP b le_rfl
    rw [hz, Polynomial.eval_zero] at he
    exact hpos.ne' (Nat.cast_eq_zero.mp he)
  have hlc : 0 < P.leadingCoeff := lt_of_le_of_ne
    (PolynomialGrowthDegree.Construction.polynomial_leadingCoeff_nonneg_of_eventually_nat_eval_nonneg P b
      (fun n hn => (hP n hn) ▸ Nat.cast_nonneg _))
    (Polynomial.leadingCoeff_ne_zero.mpr hp0).symm
  have hd : P.natDegree = g := by
    apply PolynomialGrowthDegree.Construction.polynomial_natDegree_eq_of_power_growth P hlc g b c₁ c₂ D hc₁ hc₂
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

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FilteredHilbertDimension.Construction
