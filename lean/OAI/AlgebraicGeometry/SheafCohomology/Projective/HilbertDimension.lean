import OAI.AlgebraicGeometry.SheafCohomology.Projective.FilteredSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FilteredHilbertDimension

/-! # Hilbert Dimension -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.HilbertDimension.Dimension

noncomputable section

/-! The Hilbert polynomial of actual projective sections has the affine chart's Krull dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
    {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem closedProjective_Hilbert_leadingCoeff_pos
    (hfield : IsField Γ(Spec (.of R), ⊤)) {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f] (j : σ)
    [Nonempty (f ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j)] (P : Polynomial ℚ) (b : ℕ)
    (hP : ∀ n : ℕ, b ≤ n →
      (Module.finrank Γ(Spec (.of R), ⊤)
        ((AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
          ((Scheme.Modules.pullback f).obj (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n))) : ℚ) =
        P.eval (n : ℚ)) : 0 < P.leadingCoeff := by
  let := hfield.toField
  let := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (f ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  obtain ⟨c, hc⟩ := FilteredSections.Dimension.closedProjective_sections_filtered_finrank hfield f j
  apply FilteredHilbertDimension.Dimension.polynomialFilteredPiece_Hilbert_leadingCoeff_pos Γ(Spec (.of R), ⊤)
    Γ(X, f ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j) (FilteredSections.Dimension.closedProjectiveChartCoordinates f j) P (max b c)
  intro n hn
  rw [← hc n ((le_max_right b c).trans hn)]
  exact hP n ((le_max_left b c).trans hn)

theorem closedProjective_Hilbert_natDegree
    (hfield : IsField Γ(Spec (.of R), ⊤)) {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f] (j : σ)
    [Nonempty (f ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j)] (P : Polynomial ℚ) (b : ℕ)
    (hP : ∀ n : ℕ, b ≤ n →
      (Module.finrank Γ(Spec (.of R), ⊤)
        ((AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
          ((Scheme.Modules.pullback f).obj (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n))) : ℚ) =
        P.eval (n : ℚ)) :
    (P.natDegree : WithBot ℕ∞) = ringKrullDim Γ(X, f ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j) := by
  let := hfield.toField
  let := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (f ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  let φ := ChartScalars.Dimension.closedProjectiveChartPolynomialAlgHom f j
  have hφ : Function.Surjective φ := ChartScalars.Dimension.closedProjectiveChartPolynomialAlgHom_surjective f j
  have : Algebra.FiniteType Γ(Spec (.of R), ⊤) Γ(X, f ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j) :=
    Algebra.FiniteType.of_surjective φ hφ
  have hv : Algebra.adjoin Γ(Spec (.of R), ⊤) (Set.range (FilteredSections.Dimension.closedProjectiveChartCoordinates f j)) = ⊤ :=
    HomogeneousQuotientFiltration.Dimension.adjoin_polynomial_generators_of_surjective φ hφ
  obtain ⟨c, hc⟩ := FilteredSections.Dimension.closedProjective_sections_filtered_finrank hfield f j
  apply FilteredHilbertDimension.Dimension.polynomialFilteredPiece_Hilbert_natDegree Γ(Spec (.of R), ⊤)
    Γ(X, f ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j) (FilteredSections.Dimension.closedProjectiveChartCoordinates f j) hv P (max b c)
  intro n hn
  rw [← hc n ((le_max_right b c).trans hn)]
  exact hP n ((le_max_left b c).trans hn)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.HilbertDimension.Dimension
