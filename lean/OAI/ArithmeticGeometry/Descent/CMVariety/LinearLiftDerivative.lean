import OAI.ArithmeticGeometry.Descent.CMVariety.IntegralMarkedMaps

/-! # Linear Lift Derivative -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.LinearLiftDerivative.Abelian.IntrinsicPeriods

noncomputable section

/-!
The native linear lift of an actual algebraic group morphism is its
actual manifold differential at the identity. This identifies the
lifted period images used in the continuity proof with derivatives of
the genuine scheme map, rather than a freely chosen linear family.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : T2Space (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) :=
  A.variety.presentation.complexPoints_t2Space

theorem algebraicLinearLift_exp {A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (f : A.toOver ⟶ B.toOver) [IsMonHom f] (v : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (E := AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)
      (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) v) =
        AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (E := AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver)
          (IntegralMarkedMaps.Abelian.IntrinsicPeriods.algebraicLinearLift f v) := by
  change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f
      (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A).proj v)) =
    AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B).proj (IntegralMarkedMaps.Abelian.IntrinsicPeriods.algebraicLinearLift f v))
  rw [← IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.nativeMap_algebraicTorusMap f, AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.nativeMap_periodHomeomorph]
  exact congrArg (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B) (IntegralMarkedMaps.Abelian.IntrinsicPeriods.algebraicLinearLift_lifts f v)

/-- The derivative at the identity, in the actual native tangent models,
equals the real restriction of the proved complex-linear lift. -/
theorem algebraicLinearLift_eq_mfderiv {A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (f : A.toOver ⟶ B.toOver) [IsMonHom f] (v : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
    mfderiv (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B))
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) (1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) v =
        IntegralMarkedMaps.Abelian.IntrinsicPeriods.algebraicLinearLift f v := by
  let L := (IntegralMarkedMaps.Abelian.IntrinsicPeriods.algebraicLinearLift f).toContinuousLinearMap.restrictScalars ℝ
  let expA := AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (E := AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
  let expB := AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (E := AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver)
  have hfun : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ∘ expA = expB ∘ L :=
    funext (algebraicLinearLift_exp f)
  have hleft := mfderiv_comp (I := 𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A))
    (I' := 𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) (I'' := 𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B)) (0 : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)
    (((AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.real_contMDiff_map f ∞).mdifferentiable (by simp)) (expA 0))
    (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap_mdifferentiable (E := AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) 0)
  have hright := mfderiv_comp (I := 𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A))
    (I' := 𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B)) (I'' := 𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B)) (0 : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)
    (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap_mdifferentiable (E := AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver) (L 0))
    L.mdifferentiableAt
  have he := congrArg (fun k : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver =>
    (show AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →L[ℝ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B from
      mfderiv (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B)) k 0)) hfun
  rw [hleft, hright] at he
  have hA := (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.hasMFDerivAt_expMap_zero
    (E := AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)).mfderiv
  have hB := (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.hasMFDerivAt_expMap_zero
    (E := AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver)).mfderiv
  have hzero : expA 0 = 1 := AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp_zero
  have hL : mfderiv (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B)) L 0 = L :=
    L.hasMFDerivAt.mfderiv
  erw [hA, map_zero, hB, hL, hzero] at he
  exact congrArg (fun k => k v) he

end

end OAI.ArithmeticGeometry.Descent.CMVariety.LinearLiftDerivative.Abelian.IntrinsicPeriods
