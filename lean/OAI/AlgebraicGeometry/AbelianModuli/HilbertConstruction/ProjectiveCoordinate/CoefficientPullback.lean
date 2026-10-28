import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.CoordinatePullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality

/-! # Coefficient Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.CoefficientPullback

noncomputable section

/-! Projective coefficient maps preserve the actual standard coordinate opens and regular coordinate-ratio functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R A : CommRingCat.{u}} (φ : R ⟶ A) {n : ℕ}

theorem polynomialProjectiveMap_coordinate_preimage (i : Fin (n + 1)) :
    Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n ⁻¹ᵁ Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i) =
      Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n) (X i) := by
  let : Algebra R A := φ.hom.toAlgebra
  have he := Proj.map_preimage_basicOpen (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (n := n) φ.hom)
    (Polynomial.ProjectiveCoefficients.polynomial_irrelevant_coefficient (R := R) (A := A) (n := n)) (X i)
  exact he.trans (congrArg (Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n)) (map_X φ.hom i))

theorem polynomialProjectiveMap_coordinate_pullback (i j : Fin (n + 1))
    (h : Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n) (X i) ≤
      Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n ⁻¹ᵁ Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i)) :
    (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n).appLE (Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i))
      (Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n) (X i)) h (Quotient.CoordinatePullback.projectiveCoordinateFunction R i j) =
      Quotient.CoordinatePullback.projectiveCoordinateFunction A i j := by
  let : Algebra R A := φ.hom.toAlgebra
  let g := HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (n := n) φ.hom
  have hxi : X i ∈ HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n 1 := isHomogeneous_X R i
  have hxj : X j ∈ HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n (1 • (1 : ℕ)) := isHomogeneous_X R j
  have he := Proj.awayToSection_comp_appLE g
    (Polynomial.ProjectiveCoefficients.polynomial_irrelevant_coefficient (R := R) (A := A) (n := n)) hxi
  have hv := ConcreteCategory.congr_hom he
    (HomogeneousLocalization.Away.mk (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) hxi 1 (X j) hxj)
  change (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n).appLE (Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i))
      (Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n) (g (X i))) _ (Quotient.CoordinatePullback.projectiveCoordinateFunction R i j) =
    Proj.awayToSection (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n) (g (X i))
      (HomogeneousLocalization.Away.map g (X i)
        (HomogeneousLocalization.Away.mk (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) hxi 1 (X j) hxj)) at hv
  rw [HomogeneousLocalization.Away.map_mk] at hv
  let P (z w : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n 1) : Prop := ∀ hz : Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n) z.val ≤
      Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n ⁻¹ᵁ Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i),
    (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n).appLE (Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i))
      (Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n) z.val) hz (Quotient.CoordinatePullback.projectiveCoordinateFunction R i j) =
      Proj.awayToSection (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n) z.val
        (HomogeneousLocalization.Away.mk (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n) z.property 1 w.val w.property)
  have hp : P ⟨g (X i), g.map_mem hxi⟩ ⟨g (X j), g.map_mem hxj⟩ := by
    intro hz
    exact hv
  have hi' : (⟨g (X i), g.map_mem hxi⟩ : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n 1) = ⟨X i, isHomogeneous_X A i⟩ :=
    Subtype.ext (map_X φ.hom i)
  have hj' : (⟨g (X j), g.map_mem hxj⟩ : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n 1) = ⟨X j, isHomogeneous_X A j⟩ :=
    Subtype.ext (map_X φ.hom j)
  exact ((congrArg₂ P hi' hj').mp hp) h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.CoefficientPullback
