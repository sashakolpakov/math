import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.ChartBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Terms
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Cech Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.CechBaseChange.GradedHilbert

noncomputable section

/-! Base change of actual finite homogeneous Čech terms of a coordinate quotient. -/

open _root_.MvPolynomial TensorProduct

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech

universe u v

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S] {n : ℕ}

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))

def coordinateModuleCechTermBaseChangeEquiv (d : ℤ) (q : ℕ) :
    S ⊗[R] ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := Fin (n + 1)) R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q ≃ₗ[R]
      ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := Fin (n + 1)) S (Hilbert.Polynomial.GradedHilbert.CoordinateRing S n ⧸ (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal)
        (IntegerQuotient.GradedHilbert.integerQuotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)) d q :=
  ((ModuleCech.Terms.ProjectiveCech.moduleCechTermEquiv (σ := Fin (n + 1)) R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q).lTensor S).trans
    ((TensorProduct.piRight R R S (fun s : {s : Finset (Fin (n + 1)) // s.card = q} =>
      Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (IntegerQuotient.GradedHilbert.integerQuotientGrading I) s.val d)).trans
      ((LinearEquiv.piCongrRight (fun s : {s : Finset (Fin (n + 1)) // s.card = q} =>
        ChartBaseChange.GradedHilbert.coordinateModuleChartDegreeBaseChangeEquiv (S := S) I s.val d)).trans
        ((ModuleCech.Terms.ProjectiveCech.moduleCechTermEquiv (σ := Fin (n + 1)) S (Hilbert.Polynomial.GradedHilbert.CoordinateRing S n ⧸ (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal)
          (IntegerQuotient.GradedHilbert.integerQuotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)) d q).symm.restrictScalars R)))

theorem coordinateModuleCechTermBaseChangeEquiv_tmul (d : ℤ) (q : ℕ) (r : S)
    (f : ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := Fin (n + 1)) R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q)
    (s : Finset (Fin (n + 1))) :
    (coordinateModuleCechTermBaseChangeEquiv (S := S) I d q (r ⊗ₜ[R] f)).val s =
      ChartBaseChange.GradedHilbert.coordinateModuleChartBaseChangeEquiv (S := S) I s (r ⊗ₜ[R] f.val s) := by
  classical
  by_cases hs : s.card = q
  · change (if h : s.card = q then
      (ChartBaseChange.GradedHilbert.coordinateModuleChartDegreeBaseChangeEquiv (S := S) I s d
        (r ⊗ₜ[R] (⟨f.val s, f.property.1 s⟩ : Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R
          (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (IntegerQuotient.GradedHilbert.integerQuotientGrading I) s d))).val else 0) = _
    rw [dite_eq_left hs, ChartBaseChange.GradedHilbert.coordinateModuleChartDegreeBaseChangeEquiv_val, LinearMap.lTensor_tmul]
    rfl
  · rw [(coordinateModuleCechTermBaseChangeEquiv (S := S) I d q (r ⊗ₜ[R] f)).property.2 s hs,
      f.property.2 s hs, TensorProduct.tmul_zero, LinearEquiv.map_zero]

theorem coordinateModuleCechTermBaseChangeEquiv_differential (d : ℤ) (q : ℕ)
    (x : S ⊗[R] ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := Fin (n + 1)) R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q) :
    coordinateModuleCechTermBaseChangeEquiv (S := S) I d (q + 1)
      ((ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
        (IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q).lTensor S x) =
      ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) S
        (Hilbert.Polynomial.GradedHilbert.CoordinateRing S n ⧸ (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal)
        (IntegerQuotient.GradedHilbert.integerQuotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)) d q
        (coordinateModuleCechTermBaseChangeEquiv (S := S) I d q x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r f =>
    apply Subtype.ext
    funext s
    rw [LinearMap.lTensor_tmul, coordinateModuleCechTermBaseChangeEquiv_tmul]
    change ChartBaseChange.GradedHilbert.coordinateModuleChartBaseChangeEquiv (S := S) I s
      (r ⊗ₜ[R] (∑ i ∈ s, Cech.Signs.ProjectiveCech.alternatingSign R s i •
        Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Finset.erase_subset i s) (f.val (s.erase i)))) =
      ∑ i ∈ s, Cech.Signs.ProjectiveCech.alternatingSign S s i •
        Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction S (Hilbert.Polynomial.GradedHilbert.CoordinateRing S n ⧸ (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal)
          (Finset.erase_subset i s) ((coordinateModuleCechTermBaseChangeEquiv (S := S) I d q (r ⊗ₜ[R] f)).val (s.erase i))
    rw [TensorProduct.tmul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [coordinateModuleCechTermBaseChangeEquiv_tmul, TensorProduct.tmul_smul, map_smul,
      ← LinearMap.lTensor_tmul, ChartBaseChange.GradedHilbert.coordinateModuleChartBaseChangeEquiv_restriction,
      ← algebraMap_smul S, CoefficientModuleCharts.ProjectiveCech.alternatingSign_algebraMap]
  | add x y hx hy => simp only [LinearEquiv.map_add, LinearMap.map_add, hx, hy]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.CechBaseChange.GradedHilbert
