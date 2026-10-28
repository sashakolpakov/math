import OAI.RepresentationTheory.Theta.Geometric.PointCharts
import OAI.RepresentationTheory.Theta.Geometric.ChartNaturality

/-! # Point Naturality -/

namespace OAI.RepresentationTheory.Theta.Geometric.PointNaturality

noncomputable section

/-! The point-defined geometric charts commute with genuine algebra
morphisms, without an externally selected evaluation algebra. -/

open scoped TensorProduct
open _root_.CategoryTheory

variable (F : Type) [Field F] [Algebra ℂ F]
  {A B : Type} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
  [Algebra.Smooth ℂ A] [Algebra.Smooth ℂ B] {n m : ℕ}
  (h : A →ₐ[ℂ] B)
  (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin n → ℂ))
  (f : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin m → ℂ))
  (he : e ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas B n) (hf : f ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A m)
  (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (hx : x ∈ e.source) (hfx : x.comp h ∈ f.source)

theorem pointChartGeometric_naturality (z : F ⊗[ℂ] (Fin n → ℂ)) :
    (PointCharts.pointChartGeometricEquiv F f hf (x.comp h) hfx
      ((fderiv ℂ (fun w => f ((e.symm w).comp h)) (e x)).toLinearMap.baseChange F z)).val =
      (PointCharts.pointChartGeometricEquiv F e he x hx z).val ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A B h := by
  let : Algebra A B := h.toRingHom.toAlgebra
  let : IsScalarTower ℂ A B := IsScalarTower.of_algHom h
  let : Algebra B ℂ := x.toRingHom.toAlgebra
  let : IsScalarTower ℂ B ℂ := IsScalarTower.of_algHom x
  let : Algebra A ℂ := (x.comp h).toRingHom.toAlgebra
  let : IsScalarTower ℂ A ℂ := IsScalarTower.of_algHom (x.comp h)
  let xF : B →ₐ[ℂ] F := (Algebra.ofId ℂ F).comp x
  let yF : A →ₐ[ℂ] F := (Algebra.ofId ℂ F).comp (x.comp h)
  let : Algebra B F := xF.toRingHom.toAlgebra
  let : Algebra A F := yF.toRingHom.toAlgebra
  let : IsScalarTower ℂ B F := IsScalarTower.of_algHom xF
  let : IsScalarTower ℂ A F := IsScalarTower.of_algHom yF
  let : IsScalarTower B ℂ F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower A ℂ F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower A B F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hmap : IsScalarTower.toAlgHom ℂ A B = h := AlgHom.ext (fun _ => rfl)
  have hfx' : x.comp (IsScalarTower.toAlgHom ℂ A B) ∈ f.source := by rwa [hmap]
  have ht := ChartNaturality.geometricChartTangent_naturality F e f he hf x hx hfx' (fun _ => rfl) (fun _ => rfl) z
  simp only [hmap] at ht
  rw [PointCharts.pointChartGeometricEquiv_apply, PointCharts.pointChartGeometricEquiv_apply]
  exact (congrArg (fun t : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (DualNumber F) ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A =>
    (TangentSources.geometricDualNumberIso ℂ F).inv ≫ t) ht).trans (Category.assoc _ _ _).symm

end

end OAI.RepresentationTheory.Theta.Geometric.PointNaturality
