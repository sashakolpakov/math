import OAI.RepresentationTheory.Theta.Geometric.TangentScalars
import OAI.RepresentationTheory.Theta.Geometric.OpenNaturality
import OAI.RepresentationTheory.Theta.Geometric.GroupDerivative

/-! # Naturality -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.Naturality.IntrinsicTangentChart

noncomputable section

/-! Scalar extension of the native derivative is the actual morphism on
all extended-field infinitesimal scheme points. -/

open scoped TensorProduct _root_.Manifold
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  {p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X} (C : TangentCharts.NativeTangentChart X p)
  (F : Type) [Field F] [Algebra ℂ F]
  (φ : X ⟶ Y) (D : TangentCharts.NativeTangentChart Y (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ p))

local notation "ModelX" => OAI.RepresentationTheory.Theta.Geometric.GroupDerivative.nativeTangentModel X
local notation "ModelY" => OAI.RepresentationTheory.Theta.Geometric.GroupDerivative.nativeTangentModel Y

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TangentCharts.NativeTangentChart.geometricTangentEquiv_naturality (v : F ⊗[ℂ] ModelX) :
    (D.geometricTangentEquiv F
      ((mfderiv 𝓘(ℂ, ModelX) 𝓘(ℂ, ModelY) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ) p).toLinearMap.baseChange F v)).val =
        (C.geometricTangentEquiv F v).val ≫ φ := by
  have hxy : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap D.algebra
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y D.U D.affine) D.point =
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap C.algebra
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X C.U C.affine ≫ φ) C.point := by
    rw [AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp]
    exact D.point_eq.trans (congrArg (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ) C.point_eq).symm
  have hder := congrArg (fun l : ModelX →L[ℂ] ModelY => l.toLinearMap.baseChange F v)
    (C.mfderiv_charts φ D)
  have ht := OpenNaturality.pointChartGeometric_schemeMap F C.algebra D.algebra
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X C.U C.affine ≫ φ)
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y D.U D.affine)
    C.chart D.chart C.regular D.regular C.point C.source D.point D.source hxy v
  exact (congrArg (fun w : F ⊗[ℂ] ModelY => (D.geometricTangentEquiv F w).val) hder).trans
    ((D.geometricTangentEquiv_pointChart F _).trans (ht.trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun q : LieFieldTests.extendedDualTest ℂ F ⟶ X => q ≫ φ)
          (C.geometricTangentEquiv_pointChart F v).symm))))

omit D in
theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TangentCharts.NativeTangentChart.geometricTangentEquiv_naturality_of_point {q : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y}
    (D : TangentCharts.NativeTangentChart Y q) (hpq : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ p = q) (v : F ⊗[ℂ] ModelX) :
    (D.geometricTangentEquiv F
      ((mfderiv 𝓘(ℂ, ModelX) 𝓘(ℂ, ModelY) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ) p).toLinearMap.baseChange F v)).val =
        (C.geometricTangentEquiv F v).val ≫ φ := by
  subst q
  exact C.geometricTangentEquiv_naturality F φ D v

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.Naturality.IntrinsicTangentChart
