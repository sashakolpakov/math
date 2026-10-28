import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FiniteKernel
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Complex Fibers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.ComplexFibers

noncomputable section

/-! Finite scheme morphisms have finite fibers on actual complex
points. The proof uses closed-point injectivity and the genuine finite
scheme fibers, so no finiteness assumption on analytic points is needed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem complexPoint_underlying_injective (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] :
    Function.Injective (fun x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X => x.left (IsLocalRing.closedPoint ℂ)) := by
  intro x y hxy
  apply Over.OverMorphism.ext
  exact ext_of_apply_closedPoint_eq X.hom x.w y.w hxy

theorem complexPoints_finite_fiber {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType X.hom]
    (f : X ⟶ Y) [LocallyQuasiFinite f.left] [QuasiCompact f.left] (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) :
    {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x = y}.Finite := by
  let j : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → X.left := fun x => x.left (IsLocalRing.closedPoint ℂ)
  have hm : Set.MapsTo j {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x = y}
      (f.left ⁻¹' {y.left (IsLocalRing.closedPoint ℂ)}) := by
    intro x hx
    exact congrArg (fun q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y => q.left (IsLocalRing.closedPoint ℂ)) hx
  exact Set.Finite.of_injOn hm (complexPoint_underlying_injective X).injOn
    (f.left.finite_preimage_singleton _)

namespace NativeLinearMaps

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

variable {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (f : A.toOver ⟶ B.toOver) [IsMonHom f] [IsFinite f.left]

theorem linearLift_injective_of_isFinite : Function.Injective (Intrinsic.Maps.IntrinsicLinearMaps.linearLift f) := by
  exact Intrinsic.FiniteKernel.IntrinsicLinearMaps.linearLift_injective_of_finite_native_kernel f (complexPoints_finite_fiber f 1)

theorem rationalLift_injective_of_isFinite : Function.Injective (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f) := by
  exact Intrinsic.FiniteKernel.IntrinsicLinearMaps.rationalLift_injective_of_finite_native_kernel f (complexPoints_finite_fiber f 1)

end NativeLinearMaps

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.ComplexFibers
