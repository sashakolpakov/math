import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.CechBaseChange

/-! # Cech Tensor Exactness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.CechTensorExactness.GradedHilbert

noncomputable section

/-! Exactness of tensor Čech complexes is equivalent to exactness of the actual coefficient-base-changed coordinate quotient. -/

open _root_.MvPolynomial TensorProduct

universe u v

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))

theorem coordinateCech_tensor_exact_iff (d : ℤ) (q : ℕ) :
    Function.Exact ((ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q).lTensor S)
      ((ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
        (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (IntegerQuotient.GradedHilbert.integerQuotientGrading I) d (q + 1)).lTensor S) ↔
    Function.Exact (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) S
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing S n ⧸ (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal)
      (IntegerQuotient.GradedHilbert.integerQuotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)) d q)
      (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) S
        (Hilbert.Polynomial.GradedHilbert.CoordinateRing S n ⧸ (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal)
        (IntegerQuotient.GradedHilbert.integerQuotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)) d (q + 1)) := by
  apply AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
    ((ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q).lTensor S).toAddMonoidHom
    ((ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (IntegerQuotient.GradedHilbert.integerQuotientGrading I) d (q + 1)).lTensor S).toAddMonoidHom
    (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential S (Hilbert.Polynomial.GradedHilbert.CoordinateRing S n ⧸ (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal)
      (IntegerQuotient.GradedHilbert.integerQuotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)) d q).toAddMonoidHom
    (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential S (Hilbert.Polynomial.GradedHilbert.CoordinateRing S n ⧸ (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal)
      (IntegerQuotient.GradedHilbert.integerQuotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)) d (q + 1)).toAddMonoidHom
    (CechBaseChange.GradedHilbert.coordinateModuleCechTermBaseChangeEquiv (S := S) I d q).toLinearMap.toAddMonoidHom
    (CechBaseChange.GradedHilbert.coordinateModuleCechTermBaseChangeEquiv (S := S) I d (q + 1)).toLinearMap.toAddMonoidHom
    (CechBaseChange.GradedHilbert.coordinateModuleCechTermBaseChangeEquiv (S := S) I d (q + 1 + 1)).toLinearMap.toAddMonoidHom
  · apply AddMonoidHom.ext
    intro x
    exact (CechBaseChange.GradedHilbert.coordinateModuleCechTermBaseChangeEquiv_differential (S := S) I d q x).symm
  · apply AddMonoidHom.ext
    intro x
    exact (CechBaseChange.GradedHilbert.coordinateModuleCechTermBaseChangeEquiv_differential (S := S) I d (q + 1) x).symm
  · exact (CechBaseChange.GradedHilbert.coordinateModuleCechTermBaseChangeEquiv (S := S) I d q).surjective
  · exact (CechBaseChange.GradedHilbert.coordinateModuleCechTermBaseChangeEquiv (S := S) I d (q + 1)).bijective
  · exact (CechBaseChange.GradedHilbert.coordinateModuleCechTermBaseChangeEquiv (S := S) I d (q + 1 + 1)).injective

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.CechTensorExactness.GradedHilbert
