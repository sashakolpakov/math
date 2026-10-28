import OAI.RepresentationTheory.Theta.Geometric.IntrinsicTangentNaturality
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! # Group Derivative -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The native manifold derivative at the identity is a functor on actual
group-scheme morphisms. Its naturality is the proved dual-number comparison. -/

open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj
open _root_.CategoryTheory _root_.AlgebraicGeometry

abbrev GroupDerivative.nativeTangentModel (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom] :=
  Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ

variable {X Y Z : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
  [IsIntegral X.left] [Smooth X.hom] [MonObj X]
  [IsIntegral Y.left] [Smooth Y.hom] [MonObj Y]
  [IsIntegral Z.left] [Smooth Z.hom] [MonObj Z]

def GroupDerivative.nativeGroupDerivative (f : X ⟶ Y) : GroupDerivative.nativeTangentModel X →L[ℂ] GroupDerivative.nativeTangentModel Y :=
  mfderiv 𝓘(ℂ, GroupDerivative.nativeTangentModel X) 𝓘(ℂ, GroupDerivative.nativeTangentModel Y) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) 1

theorem GroupDerivative.nativeGroupDerivative_id :
    GroupDerivative.nativeGroupDerivative (𝟙 X) = ContinuousLinearMap.id ℂ (GroupDerivative.nativeTangentModel X) := by
  have hf : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (𝟙 X) = id := funext (fun x => Category.comp_id x)
  unfold GroupDerivative.nativeGroupDerivative
  rw [hf, mfderiv_id]
  rfl

theorem GroupDerivative.nativeGroupDerivative_one : GroupDerivative.nativeGroupDerivative (1 : X ⟶ Y) = 0 := by
  have hf : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (1 : X ⟶ Y) = fun _ => (1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) :=
    funext (fun x => MonObj.comp_one x)
  unfold GroupDerivative.nativeGroupDerivative
  rw [hf, mfderiv_const]
  rfl

omit [MonObj Z] in
theorem GroupDerivative.nativeGroupDerivative_comp (f : X ⟶ Y) (g : Y ⟶ Z) [IsMonHom f] :
    GroupDerivative.nativeGroupDerivative (f ≫ g) = (GroupDerivative.nativeGroupDerivative g).comp (GroupDerivative.nativeGroupDerivative f) := by
  have hf := (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map f ∞).mdifferentiableAt (x := (1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (by simp)
  have hg := (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map g ∞).mdifferentiableAt
    (x := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (by simp)
  have hcomp : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (f ≫ g) =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g ∘ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f :=
    funext (fun x => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp f g x)
  have hone : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) = 1 := MonObj.one_comp f
  have hd := mfderiv_comp (1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) hg hf
  rw [← hcomp, hone] at hd
  exact hd

omit [MonObj Z] in
theorem GroupDerivative.nativeGroupDerivative_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) [IsMonHom f]
    (v : GroupDerivative.nativeTangentModel X) :
    GroupDerivative.nativeGroupDerivative g (GroupDerivative.nativeGroupDerivative f v) = GroupDerivative.nativeGroupDerivative (f ≫ g) v :=
  congrArg (fun l : GroupDerivative.nativeTangentModel X →L[ℂ] GroupDerivative.nativeTangentModel Z => l v)
    (GroupDerivative.nativeGroupDerivative_comp f g).symm

theorem Intrinsic.TangentCharts.NativeTangentChart.groupDerivative_naturality (C : Intrinsic.TangentCharts.NativeTangentChart X 1)
    (D : Intrinsic.TangentCharts.NativeTangentChart Y 1) (f : X ⟶ Y) [IsMonHom f] (v : GroupDerivative.nativeTangentModel X) :
    (D.tangentEquiv (GroupDerivative.nativeGroupDerivative f v)).val = (C.tangentEquiv v).val ≫ f :=
  C.tangentEquiv_naturality_of_point f D (MonObj.one_comp f) v

end

end OAI.RepresentationTheory.Theta.Geometric
