import OAI.AlgebraicGeometry.Comparison.Betti.NormalizedHomogeneousPolynomials

/-! # Negative Polynomial Coefficient Equiv -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.NegativePolynomialCoefficientEquiv.Dolbeault

noncomputable section

/-! Full-negative entire coefficients are linearly equivalent to normalized homogeneous polynomials. -/

theorem negativePolynomialCoefficientMap_injective (N k : ℕ) :
    Function.Injective (NormalizedHomogeneousPolynomials.Dolbeault.negativePolynomialCoefficientMap N k) := by
  intro P Q h
  apply Subtype.ext
  apply P.property.1.funext Q.property.1
  intro x
  exact congrArg (fun a : HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset (Fin N)) (-(k : ℤ)) =>
    Laurent.SectorSum.Dolbeault.laurentEntireFunction a.val x) h

theorem negativePolynomialCoefficientMap_surjective (N k : ℕ) :
    Function.Surjective (NormalizedHomogeneousPolynomials.Dolbeault.negativePolynomialCoefficientMap N k) := by
  intro a
  obtain ⟨P, hP, he⟩ := Laurent.CoefficientPolynomials.Dolbeault.fullNegativeCoefficient_exists_polynomial_nonpos (-(k : ℤ)) (by omega) a
  have hPk : P.IsHomogeneous k := by simpa only [neg_neg, Int.toNat_natCast] using hP
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin N)), ∀ x : Fin N → ℂ,
      x i = 0 → MvPolynomial.eval x P = 0 := by
    intro i hi x hx
    exact (he x).trans (a.property.1 i hi ⟨x, trivial⟩ hx)
  refine ⟨⟨P, hPk, hz⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact he x.val

def negativePolynomialCoefficientEquiv (N k : ℕ) :
    NormalizedHomogeneousPolynomials.Dolbeault.normalizedHomogeneousPolynomials (Finset.univ : Finset (Fin N)) k ≃ₗ[ℂ]
      HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset (Fin N)) (-(k : ℤ)) :=
  LinearEquiv.ofBijective (NormalizedHomogeneousPolynomials.Dolbeault.negativePolynomialCoefficientMap N k)
    ⟨negativePolynomialCoefficientMap_injective N k, negativePolynomialCoefficientMap_surjective N k⟩

theorem negativePolynomialCoefficientEquiv_apply (N k : ℕ)
    (P : NormalizedHomogeneousPolynomials.Dolbeault.normalizedHomogeneousPolynomials (Finset.univ : Finset (Fin N)) k) (x : Fin N → ℂ) :
    Laurent.SectorSum.Dolbeault.laurentEntireFunction (negativePolynomialCoefficientEquiv N k P).val x = MvPolynomial.eval x P.val := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.NegativePolynomialCoefficientEquiv.Dolbeault
