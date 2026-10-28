import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs

/-! # Iterated Scheme Pullback -/

namespace OAI.RepresentationTheory.Theta.Geometric.IteratedSchemePullback

noncomputable section

/-! Iterating a scheme map agrees with iteration on its complex points
and on the actual affine-test differential forms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants

def schemeEndPower {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ X) : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => f ≫ schemeEndPower f n

theorem formsPullback_schemeEndPower {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ X)
    (n : ℕ) (form : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms X) :
    AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (IteratedSchemePullback.schemeEndPower f n) form = (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback f)^[n] form := by
  induction n with
  | zero => rw [IteratedSchemePullback.schemeEndPower, AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback_id, Function.iterate_zero]; rfl
  | succ n ih =>
    rw [IteratedSchemePullback.schemeEndPower, AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback_comp, LinearMap.comp_apply, ih,
      Function.iterate_succ_apply']

theorem schemeEndPower_complexPoints {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ X)
    (n : ℕ) (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (IteratedSchemePullback.schemeEndPower f n) x =
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)^[n] x := by
  induction n generalizing x with
  | zero =>
    change x ≫ 𝟙 X = x
    exact Category.comp_id x
  | succ n ih =>
    change x ≫ (f ≫ IteratedSchemePullback.schemeEndPower f n) = _
    rw [← Category.assoc]
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (IteratedSchemePullback.schemeEndPower f n) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x) = _
    rw [ih, Function.iterate_succ_apply]

end

end OAI.RepresentationTheory.Theta.Geometric.IteratedSchemePullback
