import OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Abelian Translations M -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianTranslationsM.Constructions.AbelianTranslations

noncomputable section

/-!
# DegreeTwo: algebraic translations on the native abelian-variety manifold

These maps use the genuine algebraic group object and the native scheme-point
atlas. Their smoothness follows from the proved theorem on actual scheme maps.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

abbrev Model (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :=
  Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom) → ℂ

/-- Translation is itself a morphism of the underlying scheme. -/
def leftTranslation (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) :
    A.toOver ⟶ A.toOver := (toUnit A.toOver ≫ x) * 𝟙 A.toOver

@[simp]
theorem leftTranslation_apply (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (x y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (leftTranslation A x) y = x * y := by
  change y ≫ ((toUnit A.toOver ≫ x) * 𝟙 A.toOver) = x * y
  rw [MonObj.comp_mul]
  simp only [comp_toUnit_assoc, Category.comp_id]
  congr 1

/-- All native complex-point translations are complex analytic. -/
theorem contMDiff_leftTranslation (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) (r : ℕ∞ω) :
    ContMDiff (𝓘(ℂ, Model A)) (𝓘(ℂ, Model A)) r
      (fun y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver => x * y) := by
  have heq : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (leftTranslation A x) = fun y => x * y :=
    funext (leftTranslation_apply A x)
  rw [← heq]
  exact ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (leftTranslation A x) r

/-- Native translations are smooth on the underlying real manifold as well. -/
theorem real_contMDiff_leftTranslation (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) (r : ℕ∞ω) :
    ContMDiff (𝓘(ℝ, Model A)) (𝓘(ℝ, Model A)) r
      (fun y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver => x * y) := by
  have heq : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (leftTranslation A x) = fun y => x * y :=
    funext (leftTranslation_apply A x)
  rw [← heq]
  exact ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map (leftTranslation A x) r

/-- Inversion is complex analytic on the native manifold. -/
theorem contMDiff_inv (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (r : ℕ∞ω) :
    ContMDiff (𝓘(ℂ, Model A)) (𝓘(ℂ, Model A)) r
      (fun y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver => y⁻¹) :=
  ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (GrpObj.inv (X := A.toOver)) r

/-- Inversion is smooth on the native underlying real manifold. -/
theorem real_contMDiff_inv (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (r : ℕ∞ω) :
    ContMDiff (𝓘(ℝ, Model A)) (𝓘(ℝ, Model A)) r
      (fun y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver => y⁻¹) :=
  ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map (GrpObj.inv (X := A.toOver)) r

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianTranslationsM.Constructions.AbelianTranslations
