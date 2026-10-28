import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.CechBaseChange

/-! # Cech Scalar Linearity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.CechScalarLinearity

noncomputable section

/-! The coordinate Čech base-change equivalences are linear over the extended coefficient ring. -/

open _root_.MvPolynomial TensorProduct
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.CechBaseChange.GradedHilbert

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem coordinateChartBaseChange_smul (s : Finset (Fin (n + 1))) (a : A)
    (x : A ⊗[R] HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.ModuleChart R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) s) :
    HilbertScheme.Presentations.Coordinate.ChartBaseChange.GradedHilbert.coordinateModuleChartBaseChangeEquiv (S := A) I s (a • x) =
      a • HilbertScheme.Presentations.Coordinate.ChartBaseChange.GradedHilbert.coordinateModuleChartBaseChangeEquiv (S := A) I s x := by
  induction x using TensorProduct.inductionOn with
  | tmul b m =>
    obtain ⟨k, z, rfl⟩ := HilbertScheme.Presentations.Module.Fractions.GradedModules.moduleFractionMap_surj (R := R) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s) m
    rw [TensorProduct.smul_tmul', HilbertScheme.Presentations.Coordinate.ChartBaseChange.GradedHilbert.coordinateModuleChartBaseChangeEquiv_fraction,
      HilbertScheme.Presentations.Coordinate.ChartBaseChange.GradedHilbert.coordinateModuleChartBaseChangeEquiv_fraction]
    exact (congrArg (HilbertScheme.Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial A s) k)
      ((HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.quotientBaseChangeEquiv (S := A) I).toLinearEquiv.map_smul a (b ⊗ₜ[R] z))).trans
      ((HilbertScheme.Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial A s) k).map_smul a _)
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem coordinateCechTermBaseChange_smul (d : ℤ) (q : ℕ) (a : A)
    (x : A ⊗[R] HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := Fin (n + 1)) R
      (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q) :
    HilbertScheme.Presentations.Coordinate.CechBaseChange.GradedHilbert.coordinateModuleCechTermBaseChangeEquiv (S := A) I d q (a • x) =
      a • HilbertScheme.Presentations.Coordinate.CechBaseChange.GradedHilbert.coordinateModuleCechTermBaseChangeEquiv (S := A) I d q x := by
  induction x using TensorProduct.inductionOn with
  | tmul b f =>
    apply Subtype.ext
    funext s
    rw [TensorProduct.smul_tmul', HilbertScheme.Presentations.Coordinate.CechBaseChange.GradedHilbert.coordinateModuleCechTermBaseChangeEquiv_tmul]
    change _ = a • (HilbertScheme.Presentations.Coordinate.CechBaseChange.GradedHilbert.coordinateModuleCechTermBaseChangeEquiv (S := A) I d q (b ⊗ₜ[R] f)).val s
    rw [HilbertScheme.Presentations.Coordinate.CechBaseChange.GradedHilbert.coordinateModuleCechTermBaseChangeEquiv_tmul]
    exact coordinateChartBaseChange_smul I s a (b ⊗ₜ[R] f.val s)
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

def coordinateCechTermScalarEquiv (d : ℤ) (q : ℕ) :
    A ⊗[R] HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := Fin (n + 1)) R
      (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q ≃ₗ[A]
    HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := Fin (n + 1)) A
      (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing A n ⧸ (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I).toIdeal)
      (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)) d q where
  __ := (HilbertScheme.Presentations.Coordinate.CechBaseChange.GradedHilbert.coordinateModuleCechTermBaseChangeEquiv (S := A) I d q).toAddEquiv
  map_smul' := coordinateCechTermBaseChange_smul I d q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.CechScalarLinearity
