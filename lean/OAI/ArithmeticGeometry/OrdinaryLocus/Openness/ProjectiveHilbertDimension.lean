import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveFilteredSections
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FilteredHilbertDimension

/-! # Projective Hilbert Dimension -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveHilbertDimension.Construction

noncomputable section

/-! The Hilbert polynomial of actual projective sections has the affine chart's Krull dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
    {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem closedProjective_Hilbert_natDegree
    (hfield : IsField Γ(Spec (.of R), ⊤)) {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f] (j : σ)
    [Nonempty (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)] (P : Polynomial ℚ) (b : ℕ)
    (hP : ∀ n : ℕ, b ≤ n →
      (Module.finrank Γ(Spec (.of R), ⊤)
        ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
          ((Scheme.Modules.pullback f).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n))) : ℚ) =
        P.eval (n : ℚ)) :
    (P.natDegree : WithBot ℕ∞) = ringKrullDim Γ(X, f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j) := by
  let := hfield.toField
  let := BaseOpenSections.Construction.baseOpenSectionsAlgebra (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  let φ := ProjectiveChartScalars.Construction.closedProjectiveChartPolynomialAlgHom f j
  have hφ : Function.Surjective φ := ProjectiveChartScalars.Construction.closedProjectiveChartPolynomialAlgHom_surjective f j
  have : Algebra.FiniteType Γ(Spec (.of R), ⊤) Γ(X, f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j) :=
    Algebra.FiniteType.of_surjective φ hφ
  have hv : Algebra.adjoin Γ(Spec (.of R), ⊤) (Set.range (ProjectiveFilteredSections.Construction.closedProjectiveChartCoordinates f j)) = ⊤ :=
    HomogeneousFilteredImage.Construction.adjoin_polynomial_generators_of_surjective φ hφ
  obtain ⟨c, hc⟩ := ProjectiveFilteredSections.Construction.closedProjective_sections_filtered_finrank hfield f j
  apply FilteredHilbertDimension.Construction.polynomialFilteredPiece_Hilbert_natDegree Γ(Spec (.of R), ⊤)
    Γ(X, f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j) (ProjectiveFilteredSections.Construction.closedProjectiveChartCoordinates f j) hv P (max b c)
  intro n hn
  rw [← hc n ((le_max_right b c).trans hn)]
  exact hP n ((le_max_left b c).trans hn)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveHilbertDimension.Construction
