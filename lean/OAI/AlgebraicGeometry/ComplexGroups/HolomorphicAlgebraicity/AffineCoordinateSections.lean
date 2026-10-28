import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SchemePointSeparation
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme

/-! # Affine Coordinate Sections -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AffineCoordinateSections.Constructions.Algebraization

noncomputable section

/-!
# Pulling affine polynomial coordinates back to regular sections
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def affineCoordinatePullback
    {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine X.left]
    {R : Type} [CommRing R] [Algebra ℂ R] (f : X ⟶ Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R) :
    R →ₐ[ℂ] Γ(X.left, ⊤) :=
  (Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R Γ(X.left, ⊤)).symm ((Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv ≫ f)

theorem affineCoordinatePullback_eval
    {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine X.left]
    {R : Type} [CommRing R] [Algebra ℂ R] (f : X ⟶ Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (r : R) :
    Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X p (affineCoordinatePullback f r) =
      (Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv R).symm (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) r := by
  have hn : Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv Γ(X.left, ⊤) (Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X p) =
      p ≫ (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).hom :=
    (Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv Γ(X.left, ⊤)).apply_symm_apply _
  have heq : (Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X p).comp (affineCoordinatePullback f) =
      (Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv R).symm (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) := by
    apply (Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv R).injective
    rw [Equiv.apply_symm_apply]
    calc
      _ = Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv Γ(X.left, ⊤) (Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X p) ≫
          Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R Γ(X.left, ⊤) (affineCoordinatePullback f) :=
        ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv_comap _ _
      _ = (p ≫ (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).hom) ≫ ((Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv ≫ f) := by
        rw [hn, affineCoordinatePullback, Equiv.apply_symm_apply]
      _ = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p := by simp [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map]
  exact congrArg (fun χ : Foundations.Scheme.AffineComplexPoints.affineComplexPoints R => χ r) heq

theorem projective_chart_point_coordinates {n : ℕ} (i : Fin (n + 1))
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i))) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineChartOverMap n i) p =
      Foundations.Scheme.ProjectiveComplexPoints.projectiveComplexPointsEquiv n (Projectivization.mk ℂ
        (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i
          (ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointEquiv {j : Fin (n + 1) // j ≠ i}
            ((Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)).symm p)))
        (Foundations.Scheme.ProjectiveChartPoint.insertOne_ne_zero n i _)) := by
  let z := ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointEquiv {j : Fin (n + 1) // j ≠ i}
    ((Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)).symm p)
  let χ := (Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)).symm p
  have hχ : χ.toRingHom = MvPolynomial.eval z := by
    apply RingHom.ext
    intro r
    exact (ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointEquiv_eval χ r).symm
  have hp : Spec.map (CommRingCat.ofHom χ.toRingHom) = p.left := by
    rw [← Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv_left]
    exact congrArg Over.Hom.left
      ((Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)).apply_symm_apply p)
  rw [hχ] at hp
  apply Over.OverMorphism.ext
  change p.left ≫ Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n i =
    Foundations.Scheme.ProjectiveVectorPoint.projectiveVectorPoint (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i z) (Foundations.Scheme.ProjectiveChartPoint.insertOne_ne_zero n i z)
  rw [← hp]
  exact Foundations.Scheme.ProjectiveChartPoint.projectiveAffineChartMap_eval_eq_vectorPoint n i z (Foundations.Scheme.ProjectiveChartPoint.insertOne_ne_zero n i z)

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AffineCoordinateSections.Constructions.Algebraization
