import OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety
import OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure

/-! # Complex Base -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexBase

/-! The projective-space base morphism in ProjectiveCohomology agrees with the polynomial Proj base morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem projectiveSpaceToBase_eq_homogeneousProjπ (n : ℕ) :
    Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n =
      MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := Fin (n + 1)) := by
  unfold Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase MvPolynomialClosure.MvPolynomial.homogeneousProjπ
  congr 2

theorem exists_standardProjectiveClosedImmersion (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    ∃ (n : ℕ) (i : A.carrier ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n),
      IsClosedImmersion i ∧
      i ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := Fin (n + 1)) =
        A.variety.structureMap := by
  obtain ⟨n, i, hi, hπ⟩ := A.exists_closedImmersion
  exact ⟨n, i, hi, (by rw [← projectiveSpaceToBase_eq_homogeneousProjπ]; exact hπ)⟩

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexBase
