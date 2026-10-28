import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.KernelLinearLift
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps

/-! # Finite Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FiniteKernel.IntrinsicLinearMaps

noncomputable section

/-! Finite kernels of actual algebraic group maps give injective maps
on their native complex and rational period spaces. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps

variable {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (f : A.toOver ⟶ B.toOver) [IsMonHom f]

theorem algebraicTorusMap_finite_kernel
    (hfinite : {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x = 1}.Finite) :
    {q : (Maps.IntrinsicAlgebraicMaps.torus A).Point | Maps.IntrinsicAlgebraicMaps.algebraicTorusMap f q = 0}.Finite := by
  let j : (Maps.IntrinsicAlgebraicMaps.torus A).Point → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver := fun q => (Maps.IntrinsicAlgebraicMaps.periodAddEquiv A q).toMul
  have hj : Function.Injective j := fun x y h => (Maps.IntrinsicAlgebraicMaps.periodAddEquiv A).injective (congrArg Additive.ofMul h)
  have hm : Set.MapsTo j {q : (Maps.IntrinsicAlgebraicMaps.torus A).Point | Maps.IntrinsicAlgebraicMaps.algebraicTorusMap f q = 0}
      {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x = 1} := by
    intro q hq
    have h := (congrArg (Maps.IntrinsicAlgebraicMaps.periodAddEquiv B) hq).trans (Maps.IntrinsicAlgebraicMaps.periodAddEquiv B).map_zero
    have he := (Maps.IntrinsicAlgebraicMaps.periodAddEquiv B).apply_symm_apply (Additive.ofMul (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (j q)))
    exact congrArg Additive.toMul (he.symm.trans h)
  exact Set.Finite.of_injOn hm hj.injOn hfinite

theorem linearLift_injective_of_finite_native_kernel
    (hfinite : {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x = 1}.Finite) :
    Function.Injective (Maps.IntrinsicLinearMaps.linearLift f) :=
  ReferenceFamily.Finite.KernelLinearLift.linearLift_injective_of_finite_kernel (Maps.IntrinsicAlgebraicMaps.torus A) (Maps.IntrinsicAlgebraicMaps.torus B) (Maps.IntrinsicAlgebraicMaps.algebraicTorusMap f) (Maps.IntrinsicLinearMaps.linearLift f)
    (Maps.IntrinsicLinearMaps.linearLift_lifts f) (algebraicTorusMap_finite_kernel f hfinite)

theorem rationalLift_injective_of_finite_native_kernel
    (hfinite : {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x = 1}.Finite) :
    Function.Injective (IntegralMaps.IntrinsicLinearMaps.rationalLift f) := by
  intro x y hxy
  apply Subtype.ext
  exact linearLift_injective_of_finite_native_kernel f hfinite
    (congrArg (fun v : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B => v.val) hxy)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FiniteKernel.IntrinsicLinearMaps
