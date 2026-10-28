import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialFilteredAlgebra
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NoetherNormalizationDimension

/-! # Filtered Algebra Lower Growth -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FilteredAlgebraLowerGrowth.Dimension

noncomputable section

/-! Algebraically independent parameters force the expected lower polynomial growth. -/

open _root_.MvPolynomial

theorem polynomialFilteredPiece_finrank_eq_of_injective
    {K B σ : Type*} [Field K] [CommRing B] [Algebra K B]
    (v : σ → B) (hv : Function.Injective (MvPolynomial.aeval (R := K) v)) (n : ℕ) :
    Module.finrank K (PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v n) =
      Module.finrank K (MvPolynomial.restrictTotalDegree σ K n) :=
  (Submodule.equivMapOfInjective (MvPolynomial.aeval v).toLinearMap hv
    (MvPolynomial.restrictTotalDegree σ K n)).finrank_eq.symm

theorem polynomialFilteredPiece_independent_lower_bound
    {K B σ : Type*} [Field K] [CommRing B] [Algebra K B] [Fintype σ]
    (v : σ → B) (hv : Algebra.adjoin K (Set.range v) = ⊤)
    (g : ℕ) (φ : MvPolynomial (Fin g) K →ₐ[K] B) (hφ : Function.Injective φ) :
    ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ,
      (n + 1) ^ g ≤ Module.finrank K (PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v (n * c)) := by
  let w := fun i : Fin g => φ (MvPolynomial.X i)
  have he : MvPolynomial.aeval w = φ := (MvPolynomial.aeval_unique φ).symm
  have hw : Function.Injective (MvPolynomial.aeval (R := K) w) := he.symm ▸ hφ
  obtain ⟨c, hc, hcomp⟩ := PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece_exists_change_bound v w hv
  refine ⟨g * c + 1, Nat.zero_lt_succ _, fun n => ?_⟩
  have hlo : (n + 1) ^ g ≤ Module.finrank K (PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) w (g * n)) := by
    rw [polynomialFilteredPiece_finrank_eq_of_injective w hw]
    have h := PolynomialBoxDimension.Dimension.finrank_polynomial_restrictTotalDegree_ge K (Fin g) n
    rw [Fintype.card_fin] at h
    exact h
  have hm := Submodule.finrank_mono (hcomp (g * n))
  have hn : (g * n) * c ≤ n * (g * c + 1) := by
    calc
      (g * n) * c = n * (g * c) := by ac_rfl
      _ ≤ n * (g * c + 1) := Nat.mul_le_mul_left n (Nat.le_succ _)
  exact hlo.trans (hm.trans (Submodule.finrank_mono (PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece_mono v hn)))

universe u

theorem polynomialFilteredPiece_krullDimension_lower_growth
    (K B : Type u) [Field K] [CommRing B] [Nontrivial B]
    [Algebra K B] [Algebra.FiniteType K B]
    {σ : Type*} [Fintype σ] (v : σ → B) (hv : Algebra.adjoin K (Set.range v) = ⊤) :
    ∃ g : ℕ, ringKrullDim B = (g : WithBot ℕ∞) ∧ ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ,
      (n + 1) ^ g ≤ Module.finrank K (PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v (n * c)) := by
  obtain ⟨g, φ, hφ, _, hdim⟩ := NoetherNormalizationDimension.Dimension.noetherNormalization_krullDimension K B
  exact ⟨g, hdim, polynomialFilteredPiece_independent_lower_bound v hv g φ hφ⟩

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FilteredAlgebraLowerGrowth.Dimension
