import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.ChangeCover
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.ChangeQuotient
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.ModuleIsomorphism

/-! # Change Cech Exactness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.ChangeCechExactness.GradedHilbert

noncomputable section

/-! Actual graded Čech exactness of a homogeneous coordinate quotient is invariant under any linear coordinate change. -/

open _root_.MvPolynomial

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.ModuleIsomorphism.ProjectiveCech

universe u

variable {K : Type u} [Field K] {n : ℕ}

theorem changedIdeal_moduleCechExactAt_iff (e : Hilbert.Polynomial.GradedHilbert.grading K n 1 ≃ₗ[K] Hilbert.Polynomial.GradedHilbert.grading K n 1)
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (d : ℤ) (q : ℕ) :
    Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := Fin (n + 1)) K (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ (InfiniteFieldBound.GradedHilbert.changedIdeal e I).toIdeal)
        (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (InfiniteFieldBound.GradedHilbert.changedIdeal e I)) d q ↔
      Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := Fin (n + 1)) K (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal)
        (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q := by
  have hcover := ChangeCover.GradedHilbert.changedLinearCover_moduleCechExactAt_iff
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) e d q
  let : Module (MvPolynomial (Fin (n + 1)) K) (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal) :=
    ChangeQuotient.GradedHilbert.linearChangeQuotientModule e I
  let : SMul (MvPolynomial (Fin (n + 1)) K) (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal) :=
    (ChangeQuotient.GradedHilbert.linearChangeQuotientModule e I).toSMul
  let : IsScalarTower K (MvPolynomial (Fin (n + 1)) K) (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal) :=
    ChangeQuotient.GradedHilbert.linearChangeQuotient_scalarTower e I
  let : SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := Fin (n + 1)) K)
    (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) := ChangeQuotient.GradedHilbert.linearChangeQuotient_gradedSMul e I
  let E := ChangeQuotient.GradedHilbert.linearChangeQuotientPolynomialEquiv e I
  have h := Cech.ModuleIsomorphism.ProjectiveCech.moduleCechExactAt_iff_of_module_bijective K
    (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (InfiniteFieldBound.GradedHilbert.changedIdeal e I)) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) E.toLinearMap
    (ChangeQuotient.GradedHilbert.linearChangeQuotientEquiv_homogeneous e I) E.bijective d q
  exact h.trans hcover

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.ChangeCechExactness.GradedHilbert
