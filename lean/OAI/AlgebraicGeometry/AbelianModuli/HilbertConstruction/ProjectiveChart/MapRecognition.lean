import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Algebra
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-! # Map Recognition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.MapRecognition

noncomputable section

/-! A map from a standard projective chart is determined by its coefficient
map and normalized coordinates. The criterion applies directly to the
homogeneous-localization map induced by a graded projective morphism. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
universe u
variable {R B : Type u} [CommRing R] [CommRing B] {n : ℕ}

theorem projectiveChartRing_ringHom_ext (i : Fin (n + 1))
    {f g : Evaluation.projectiveChartRing R n i →+* B}
    (hC : ∀ r : R, f (algebraMap R (Evaluation.projectiveChartRing R n i) r) =
      g (algebraMap R (Evaluation.projectiveChartRing R n i) r))
    (hX : ∀ j : Fin (n + 1), f (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X j)) = g (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X j))) : f = g := by
  have h : f.comp (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i) = g.comp (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change f (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (C r)) = g (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (C r))
      rw [ProjectiveChart.Algebra.projectiveChart_dehomogenize_constant]
      exact hC r
    · intro j
      exact hX j
  apply RingHom.ext
  intro z
  obtain ⟨q, rfl⟩ := HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize_surjective i z
  exact RingHom.congr_fun h q

theorem projectiveChartEvaluation_of_coordinates
    (c : R →+* B) (v : Fin (n + 1) → B) (i : Fin (n + 1)) (hi : v i = 1)
    (φ : Evaluation.projectiveChartRing R n i →+* B)
    (hC : ∀ r : R, φ (algebraMap R (Evaluation.projectiveChartRing R n i) r) = c r)
    (hX : ∀ j : Fin (n + 1), φ (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X j)) = v j) :
    φ = Evaluation.projectiveChartEvaluation c v i hi := by
  let : Algebra R B := c.toAlgebra
  apply projectiveChartRing_ringHom_ext i
  · intro r
    exact (hC r).trans ((ProjectiveChart.Algebra.projectiveChartEvaluationAlg v i hi).commutes r).symm
  · intro j
    exact (hX j).trans (ProjectiveChart.Algebra.projectiveChartEvaluationAlg_coordinate (R := R) v i hi j).symm

variable {A : Type u} [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
variable (g : Projective.ProjectivePresentations.coordinateGrading R n →+*ᵍ 𝒜)
variable (hg : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant (Projective.ProjectivePresentations.coordinateGrading R n)).map g)
variable {T : Scheme.{u}}

theorem projectiveMap_chart_of_coordinates
    (c : R →+* Γ(T, ⊤)) (v : Fin (n + 1) → Γ(T, ⊤)) (i : Fin (n + 1)) (hi : v i = 1)
    (φ : HomogeneousLocalization.Away 𝒜 (g (X i)) →+* Γ(T, ⊤))
    (hC : ∀ r : R, φ (HomogeneousLocalization.Away.map g (X i)
      (algebraMap R (Evaluation.projectiveChartRing R n i) r)) = c r)
    (hX : ∀ j : Fin (n + 1), φ (HomogeneousLocalization.Away.map g (X i)
      (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X j))) = v j) :
    (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ Proj.awayι 𝒜 (g (X i))
      (g.map_mem (MvPolynomial.isHomogeneous_X R i)) Nat.zero_lt_one) ≫ Proj.map g hg =
      Evaluation.projectiveChartMap c v i hi := by
  have hφ : φ.comp (HomogeneousLocalization.Away.map g (X i)) =
      Evaluation.projectiveChartEvaluation c v i hi :=
    projectiveChartEvaluation_of_coordinates c v i hi _ hC hX
  rw [Category.assoc, Category.assoc,
    Proj.awayι_comp_map g hg Nat.zero_lt_one (X i) (MvPolynomial.isHomogeneous_X R i),
    ← Spec.map_comp_assoc]
  change T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (φ.comp (HomogeneousLocalization.Away.map g (X i)))) ≫
    Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) (X i) (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one = _
  rw [hφ]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.MapRecognition
