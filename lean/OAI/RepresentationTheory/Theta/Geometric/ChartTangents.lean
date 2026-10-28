import OAI.RepresentationTheory.Theta.Geometric.TangentSources
import OAI.RepresentationTheory.Theta.Geometric.RegularTangent

/-! # Chart Tangents -/

namespace OAI.RepresentationTheory.Theta.Geometric.ChartTangents

noncomputable section

/-! The complex regular chart gives complete tangent coordinates after
extension to any residue field, by the actual cotangent base change. -/

open scoped TensorProduct

variable (F : Type) [Field F] [Algebra ℂ F]
  {A : Type} [CommRing A] [Algebra ℂ A] [Algebra A ℂ] [IsScalarTower ℂ A ℂ]
  [Algebra A F] [IsScalarTower ℂ A F] [IsScalarTower A ℂ F]
  [Algebra.Smooth ℂ A] {n : ℕ}
  (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
  (he : e ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ e.source)
  (hscalar : ∀ a : A, algebraMap A ℂ a = x a)

def geometricChartDerivation :
    (F ⊗[ℂ] (Fin n → ℂ)) ≃ₗ[F] Derivation ℂ A F :=
  ((RegularTangent.regularChartDerivationEquiv e he x hx hscalar).baseChange ℂ F _ _).trans
    (DerivationBaseChange.pointDerivationBaseChange ℂ A F)

theorem geometricChartDerivation_tmul (c : F) (v : Fin n → ℂ) (a : A) :
    geometricChartDerivation F e he x hx hscalar (c ⊗ₜ[ℂ] v) a =
      c * algebraMap ℂ F (fderiv ℂ (fun z => e.symm z a) (e x) v) := by
  exact DerivationBaseChange.pointDerivationBaseChange_tmul ℂ A F c (RegularTangent.regularChartDerivation e he x hx hscalar v) a

def geometricChartTangentEquiv :
    (F ⊗[ℂ] (Fin n → ℂ)) ≃ AffineTangents.geometricAffineTangentPoints ℂ A F :=
  (geometricChartDerivation F e he x hx hscalar).toEquiv.trans
    (AffineTangents.geometricDerivationSpecEquiv ℂ A F)

theorem geometricChartTangentEquiv_apply (v : F ⊗[ℂ] (Fin n → ℂ)) :
    (geometricChartTangentEquiv F e he x hx hscalar v).val =
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (DualNumber F)
        (DualNumbers.geometricDerivationJet (geometricChartDerivation F e he x hx hscalar v)) := rfl

end

end OAI.RepresentationTheory.Theta.Geometric.ChartTangents
