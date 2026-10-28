import OAI.RepresentationTheory.Theta.Geometric.Period.Models

/-! # Algebraic Translation -/

namespace OAI.RepresentationTheory.Theta.Geometric.AlgebraicTranslation

noncomputable section

/-! Translation on the actual algebraic abelian model, with its exact
comparison on complex period points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

def abelianTranslation (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) : A.toOver ⟶ A.toOver :=
  (𝟙 A.toOver) * (Over.mkIdTerminal.from A.toOver ≫ p)

theorem abelianTranslation_points (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (p q : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (abelianTranslation A p) q = q * p := by
  change q ≫ ((𝟙 A.toOver) * (Over.mkIdTerminal.from A.toOver ≫ p)) = q * p
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc]
  have h : q ≫ Over.mkIdTerminal.from A.toOver = 𝟙 _ := Over.mkIdTerminal.hom_ext _ _
  rw [h, Category.id_comp]

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

theorem abelianTranslation_period {Φ : Torus.Data.CM.ProjectivePeriodData} (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (he : ∀ u v, e (u + v) = e u * e v) (a t : Φ.periodTorus) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (abelianTranslation A (e a)) (e t) = e (t + a) :=
  (abelianTranslation_points A (e a) (e t)).trans (he t a).symm

end

end OAI.RepresentationTheory.Theta.Geometric.AlgebraicTranslation
