import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientQuotientRetraction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientCechRetraction

/-! # Field Extension Cech Descent -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.FieldExtensionCechDescent.GradedHilbert

noncomputable section

/-! Graded Čech exactness of the actual homogeneous coordinate quotient descends along every coefficient field extension. -/

open _root_.MvPolynomial

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientCechRetraction.ProjectiveCech

universe u v

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L] {n : ℕ}

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem coordinate_moduleCechExactAt_of_field_extension (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n))
    (d : ℤ) (q : ℕ)
    (hL : Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := Fin (n + 1)) L
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing L n ⧸ (ScalarExtension.GradedHilbert.scalarExtendedHomogeneousIdeal (L := L) I).toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (ScalarExtension.GradedHilbert.scalarExtendedHomogeneousIdeal (L := L) I)) d q) :
    Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := Fin (n + 1)) K (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K (show (1 : L) ≠ 0 from one_ne_zero)
  exact CoefficientCechRetraction.ProjectiveCech.moduleCechExactAt_of_coefficient_retraction K L (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I)
    (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (ScalarExtension.GradedHilbert.scalarExtendedHomogeneousIdeal (L := L) I))
    (CoefficientQuotientRetraction.GradedHilbert.coefficientQuotientExtension (L := L) I) (CoefficientQuotientRetraction.GradedHilbert.coefficientQuotientRetraction I φ)
    (CoefficientQuotientRetraction.GradedHilbert.coefficientQuotientExtension_homogeneous I) (CoefficientQuotientRetraction.GradedHilbert.coefficientQuotientRetraction_extension I φ hφ) d q hL

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.FieldExtensionCechDescent.GradedHilbert
