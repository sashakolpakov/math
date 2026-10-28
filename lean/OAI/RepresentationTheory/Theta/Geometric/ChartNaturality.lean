import OAI.RepresentationTheory.Theta.Geometric.ChartTangents
import OAI.RepresentationTheory.Theta.Geometric.RegularTangentNaturality

/-! # Chart Naturality -/

namespace OAI.RepresentationTheory.Theta.Geometric.ChartNaturality

noncomputable section

/-! The extended regular-chart tangent coordinates commute with actual
affine morphisms and the scalar extension of their complex derivatives. -/

open scoped TensorProduct
open _root_.CategoryTheory

variable (F : Type) [Field F] [Algebra ℂ F]
  {A B : Type} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
  [Algebra A B] [IsScalarTower ℂ A B]
  [Algebra A ℂ] [Algebra B ℂ] [IsScalarTower ℂ A ℂ] [IsScalarTower ℂ B ℂ]
  [Algebra A F] [Algebra B F] [IsScalarTower ℂ A F] [IsScalarTower ℂ B F]
  [IsScalarTower A ℂ F] [IsScalarTower B ℂ F] [IsScalarTower A B F]
  [Algebra.Smooth ℂ A] [Algebra.Smooth ℂ B] {n m : ℕ}
  (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin n → ℂ))
  (f : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin m → ℂ))
  (he : e ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas B n) (hf : f ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A m)
  (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (hx : x ∈ e.source)
  (hfx : x.comp (IsScalarTower.toAlgHom ℂ A B) ∈ f.source)
  (hxscalar : ∀ b : B, algebraMap B ℂ b = x b)
  (hyscalar : ∀ a : A, algebraMap A ℂ a = (x.comp (IsScalarTower.toAlgHom ℂ A B)) a)

theorem geometricChartDerivation_naturality (z : F ⊗[ℂ] (Fin n → ℂ)) :
    ChartTangents.geometricChartDerivation F f hf (x.comp (IsScalarTower.toAlgHom ℂ A B)) hfx hyscalar
      ((fderiv ℂ (fun w => f ((e.symm w).comp (IsScalarTower.toAlgHom ℂ A B))) (e x)).toLinearMap.baseChange F z) =
    DerivationBaseChange.pointDerivationComap ℂ A B F (ChartTangents.geometricChartDerivation F e he x hx hxscalar z) := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul c v =>
      apply Derivation.ext
      intro a
      rw [LinearMap.baseChange_tmul, ChartTangents.geometricChartDerivation_tmul]
      change c * algebraMap ℂ F
        (fderiv ℂ (fun w => f.symm w a) (f (x.comp (IsScalarTower.toAlgHom ℂ A B)))
          (fderiv ℂ (fun w => f ((e.symm w).comp (IsScalarTower.toAlgHom ℂ A B))) (e x) v)) =
        ChartTangents.geometricChartDerivation F e he x hx hxscalar (c ⊗ₜ[ℂ] v) (algebraMap A B a)
      rw [ChartTangents.geometricChartDerivation_tmul]
      exact congrArg (fun t : ℂ => c * algebraMap ℂ F t)
        (RegularTangentNaturality.regularChart_derivative_naturality (IsScalarTower.toAlgHom ℂ A B)
          e f he hf x hx hfx a v).symm

theorem geometricChartTangent_naturality (z : F ⊗[ℂ] (Fin n → ℂ)) :
    (ChartTangents.geometricChartTangentEquiv F f hf (x.comp (IsScalarTower.toAlgHom ℂ A B)) hfx hyscalar
      ((fderiv ℂ (fun w => f ((e.symm w).comp (IsScalarTower.toAlgHom ℂ A B))) (e x)).toLinearMap.baseChange F z)).val =
    (ChartTangents.geometricChartTangentEquiv F e he x hx hxscalar z).val ≫
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A B (IsScalarTower.toAlgHom ℂ A B) := by
  exact (congrArg (fun δ : Derivation ℂ A F => (AffineTangents.geometricDerivationSpecEquiv ℂ A F δ).val)
    (geometricChartDerivation_naturality F e f he hf x hx hfx hxscalar hyscalar z)).trans
      (AffineTangents.geometricDerivationSpec_comap _)

end

end OAI.RepresentationTheory.Theta.Geometric.ChartNaturality
