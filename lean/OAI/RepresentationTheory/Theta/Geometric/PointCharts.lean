import OAI.RepresentationTheory.Theta.Geometric.ExtendedComplexPoints
import OAI.RepresentationTheory.Theta.Geometric.ChartTangents

/-! # Point Charts -/

namespace OAI.RepresentationTheory.Theta.Geometric.PointCharts

noncomputable section

/-! Regular-chart tangent coordinates with their evaluation algebras
constructed from the actual point, ready for overlap comparisons. -/

open scoped TensorProduct
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (F : Type) [Field F] [Algebra ℂ F]
  {A : Type} [CommRing A] [Algebra ℂ A] [Algebra.Smooth ℂ A] {n : ℕ}
  (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
  (he : e ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ e.source)

def pointChartGeometricEquiv :
    (F ⊗[ℂ] (Fin n → ℂ)) ≃ TangentSources.extendedSchemeTangentPoints ℂ F (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A)
      (ExtendedComplexPoints.extendedComplexPoint F (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A x)) := by
  let : Algebra A ℂ := x.toRingHom.toAlgebra
  let : IsScalarTower ℂ A ℂ := IsScalarTower.of_algHom x
  let xF : A →ₐ[ℂ] F := (Algebra.ofId ℂ F).comp x
  let : Algebra A F := xF.toRingHom.toAlgebra
  let : IsScalarTower ℂ A F := IsScalarTower.of_algHom xF
  let : IsScalarTower A ℂ F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hp : (TangentSources.geometricFieldPointIso ℂ F).inv ≫ AffineTangents.geometricAffineBasePoint ℂ A F =
      ExtendedComplexPoints.extendedComplexPoint F (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A x) := by
    have hx' : IsScalarTower.toAlgHom ℂ A ℂ = x := AlgHom.ext (fun _ => rfl)
    exact (ExtendedComplexPoints.geometricAffineBasePoint_extended F A).trans
      (congrArg (fun y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A => ExtendedComplexPoints.extendedComplexPoint F (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A y)) hx')
  exact ((ChartTangents.geometricChartTangentEquiv F e he x hx (fun _ => rfl)).trans
    (TangentSources.geometricAffineNativeEquiv ℂ F A)).trans
      (Equiv.subtypeEquivRight (fun _ => by rw [hp]))

theorem pointChartGeometricEquiv_apply (z : F ⊗[ℂ] (Fin n → ℂ)) :
    letI : Algebra A ℂ := x.toRingHom.toAlgebra
    letI : IsScalarTower ℂ A ℂ := IsScalarTower.of_algHom x
    let xF : A →ₐ[ℂ] F := (Algebra.ofId ℂ F).comp x
    letI : Algebra A F := xF.toRingHom.toAlgebra
    letI : IsScalarTower ℂ A F := IsScalarTower.of_algHom xF
    letI : IsScalarTower A ℂ F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    (pointChartGeometricEquiv F e he x hx z).val =
      (TangentSources.geometricDualNumberIso ℂ F).inv ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (DualNumber F)
        (DualNumbers.geometricDerivationJet (ChartTangents.geometricChartDerivation F e he x hx (fun _ => rfl) z)) := rfl

theorem pointChartGeometricEquiv_congr (y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hy : y ∈ e.source)
    (hxy : x = y) (v w : F ⊗[ℂ] (Fin n → ℂ)) (hvw : v = w) :
    (pointChartGeometricEquiv F e he x hx v).val =
      (pointChartGeometricEquiv F e he y hy w).val := by
  subst y
  subst w
  rfl

end

end OAI.RepresentationTheory.Theta.Geometric.PointCharts
