import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AffineCoordinateSections
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt

/-! # Segre Regular Equations -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreRegularEquations.Constructions.Algebraization

noncomputable section

/-!
# Homogeneous Segre equations as regular functions on affine charts
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization

def affineChartPointCoordinates {n : ℕ} (i : Fin (n + 1))
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i))) :
    {j : Fin (n + 1) // j ≠ i} → ℂ :=
  ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointEquiv _ ((Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)).symm p)

def normalizedCoordinateSections
    {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine T.left] {n : ℕ} (i : Fin (n + 1))
    (a : T ⟶ Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)) : Fin (n + 1) → Γ(T.left, ⊤) :=
  Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i (fun j => AffineCoordinateSections.Constructions.Algebraization.affineCoordinatePullback a (X j))

theorem normalizedCoordinateSections_eval
    {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine T.left] {n : ℕ} (i : Fin (n + 1))
    (a : T ⟶ Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i))
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints T) (j : Fin (n + 1)) :
    Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv T p (normalizedCoordinateSections i a j) =
      Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i (affineChartPointCoordinates i (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a p)) j := by
  classical
  by_cases hj : j = i
  · simp only [normalizedCoordinateSections, hj, Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne_self, map_one]
  · simp only [normalizedCoordinateSections, Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne_of_ne _ _ _ hj,
      AffineCoordinateSections.Constructions.Algebraization.affineCoordinatePullback_eval, affineChartPointCoordinates, ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointEquiv_apply]

def segreChartSection
    {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine T.left] {m n : ℕ}
    (i : Fin (m + 1)) (j : Fin (n + 1))
    (a : T ⟶ Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial m i))
    (b : T ⟶ Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n j))
    (P : MvPolynomial (Fin (m + 1) × Fin (n + 1)) ℂ) : Γ(T.left, ⊤) :=
  aeval (fun ab => normalizedCoordinateSections i a ab.1 * normalizedCoordinateSections j b ab.2) P

theorem segreChartSection_eval
    {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine T.left] {m n : ℕ}
    (i : Fin (m + 1)) (j : Fin (n + 1))
    (a : T ⟶ Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial m i))
    (b : T ⟶ Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n j))
    (P : MvPolynomial (Fin (m + 1) × Fin (n + 1)) ℂ) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints T) :
    Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv T p (segreChartSection i j a b P) =
      eval (SegreAt.Constructions.Segre.outer
        (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i (affineChartPointCoordinates i (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a p)))
        (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne j (affineChartPointCoordinates j (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map b p)))) P := by
  let χ := Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv T p
  change χ.toRingHom (eval₂ (algebraMap ℂ Γ(T.left, ⊤))
    (fun ab => normalizedCoordinateSections i a ab.1 * normalizedCoordinateSections j b ab.2) P) = _
  rw [eval₂_comp_left]
  have hc : χ.toRingHom.comp (algebraMap ℂ Γ(T.left, ⊤)) = RingHom.id ℂ := by
    apply RingHom.ext
    intro c
    exact χ.commutes c
  rw [hc, eval₂_id]
  have he : (fun ab : Fin (m + 1) × Fin (n + 1) =>
      χ.toRingHom (normalizedCoordinateSections i a ab.1 * normalizedCoordinateSections j b ab.2)) =
      SegreAt.Constructions.Segre.outer (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i (affineChartPointCoordinates i (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a p)))
        (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne j (affineChartPointCoordinates j (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map b p))) := by
    funext ab
    rw [map_mul]
    exact congrArg₂ (· * ·) (normalizedCoordinateSections_eval i a p ab.1)
      (normalizedCoordinateSections_eval j b p ab.2)
  exact congrArg (fun v => eval v P) he

theorem segreChartSection_eq_zero_iff
    {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine T.left] {m n d : ℕ}
    (i : Fin (m + 1)) (j : Fin (n + 1))
    (a : T ⟶ Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial m i))
    (b : T ⟶ Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n j))
    (P : MvPolynomial (Fin (m + 1) × Fin (n + 1)) ℂ) (hP : P.IsHomogeneous d)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints T) :
    Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv T p (segreChartSection i j a b P) = 0 ↔
      SegreAt.Constructions.Segre.segre
        ((Foundations.Scheme.ProjectiveComplexPoints.projectiveComplexPointsEquiv m).symm
          (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (a ≫ ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineChartOverMap m i) p))
        ((Foundations.Scheme.ProjectiveComplexPoints.projectiveComplexPointsEquiv n).symm
          (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (b ≫ ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineChartOverMap n j) p)) ∈
        Foundations.Scheme.ProjectiveZeroLocus.homogeneousProjectiveZeroLocus P hP := by
  rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp,
    AffineCoordinateSections.Constructions.Algebraization.projective_chart_point_coordinates, AffineCoordinateSections.Constructions.Algebraization.projective_chart_point_coordinates,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, SegreAt.Constructions.Segre.segre_mk,
    Foundations.Scheme.ProjectiveZeroLocus.mem_homogeneousProjectiveZeroLocus_mk, segreChartSection_eval]
  rfl

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreRegularEquations.Constructions.Algebraization
