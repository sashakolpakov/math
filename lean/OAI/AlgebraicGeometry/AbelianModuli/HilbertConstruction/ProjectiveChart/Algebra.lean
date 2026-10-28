import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.Projective

/-! # Algebra -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Algebra

noncomputable section

/-! Normalized projective chart evaluation as an algebra map, with an extensionality criterion. -/

open _root_.MvPolynomial _root_.HomogeneousLocalization
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.Projective.PolynomialProjective

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}

theorem projectiveChart_dehomogenize_constant (i : Fin (n + 1)) (r : R) :
    HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (C r) = algebraMap R (Evaluation.projectiveChartRing R n i) r := by
  rw [HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize_C, HilbertScheme.Presentations.Homogeneous.LocalizationFlat.GradedHilbert.homogeneousLocalization_algebraMap]
  rfl

def projectiveChartEvaluationAlg (v : Fin (n + 1) → A) (i : Fin (n + 1)) (hi : v i = 1) :
    Evaluation.projectiveChartRing R n i →ₐ[R] A where
  __ := Evaluation.projectiveChartEvaluation (algebraMap R A) v i hi
  commutes' r := by
    rw [HilbertScheme.Presentations.Homogeneous.LocalizationFlat.GradedHilbert.homogeneousLocalization_algebraMap]
    exact Evaluation.projectiveChartEvaluation_constant (algebraMap R A) v i hi r

theorem projectiveChartEvaluationAlg_coordinate (v : Fin (n + 1) → A)
    (i : Fin (n + 1)) (hi : v i = 1) (k : Fin (n + 1)) :
    projectiveChartEvaluationAlg (R := R) v i hi (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X k)) = v k := by
  rw [HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize_X]
  exact Evaluation.projectiveChartEvaluation_coordinate (algebraMap R A) v i hi k

theorem projectiveChartAlgebra_ext (i : Fin (n + 1))
    {f g : Evaluation.projectiveChartRing R n i →ₐ[R] A}
    (h : ∀ k : Fin (n + 1), f (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X k)) = g (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X k))) : f = g := by
  have he : f.toRingHom.comp (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i) = g.toRingHom.comp (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact (congrArg f (projectiveChart_dehomogenize_constant i r)).trans
        ((f.commutes r).trans ((g.commutes r).symm.trans
          (congrArg g (projectiveChart_dehomogenize_constant i r)).symm))
    · intro k
      exact h k
  apply AlgHom.ext
  intro x
  obtain ⟨p, rfl⟩ := HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize_surjective i x
  exact RingHom.congr_fun he p

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Algebra
