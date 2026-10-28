import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicDerivativeScalars

/-! # Lift Differential -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LiftDifferential.IntrinsicLinearMaps

noncomputable section

/-! The constructed complex-linear period lift of a genuine algebraic
group map is its actual native manifold differential at the identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicDerivativeScalars
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : LieGroup 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) ∞ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) :=
  HodgeConjecture.DegreeTwo.IntrinsicProductMaps.Constructions.IntrinsicAbelianLieGroup.realLieGroup A

theorem linearLift_exp (f : A.toOver ⟶ B.toOver) [IsMonHom f] (v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) v) =
      HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver) (Maps.IntrinsicLinearMaps.linearLift f v) :=
  Maps.IntrinsicLinearMaps.linearLift_period f v

theorem linearLift_real_derivative (f : A.toOver ⟶ B.toOver) [IsMonHom f] (v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
    mfderiv 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) 1 v =
      Maps.IntrinsicLinearMaps.linearLift f v := by
  let L : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →L[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B :=
    ((Maps.IntrinsicLinearMaps.linearLift f).toContinuousLinearMap).restrictScalars ℝ
  let ea := HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
  let eb := HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver)
  have he : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ∘ ea = eb ∘ L := funext (linearLift_exp f)
  have ha := HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.hasMFDerivAt_expMap_zero (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
  have hb := HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.hasMFDerivAt_expMap_zero (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver)
  have hleft := mfderiv_comp_apply (I := 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) (I' := 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A))
    (I'' := 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B)) (0 : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)
    ((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map f 1).mdifferentiableAt one_ne_zero) ha.mdifferentiableAt v
  have hright := mfderiv_comp_apply (I := 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) (I' := 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B))
    (I'' := 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B)) (0 : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)
    (show MDifferentiableAt 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) eb (L 0) from
      (L.map_zero).symm ▸ hb.mdifferentiableAt) L.hasMFDerivAt.mdifferentiableAt v
  have ht := congrArg (fun g : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver =>
    mfderiv 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) g 0 v) he
  have hl : mfderiv 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ∘ ea) 0 v =
      mfderiv 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) 1 v := by
    have hda : mfderiv 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) ea 0 v = v :=
      congrArg (fun D : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →L[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A => D v) ha.mfderiv
    have harg := congrArg (fun w : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A =>
      mfderiv 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) (ea 0) w) hda
    have hea : ea 0 = 1 := HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp_zero (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) (G := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    exact hleft.trans (harg.trans (congrArg (fun p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver =>
      mfderiv 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) p v) hea))
  have hr : mfderiv 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) (eb ∘ L) 0 v = L v := by
    have hdl : mfderiv 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) L 0 v = L v :=
      congrArg (fun D : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →L[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B => D v) L.hasMFDerivAt.mfderiv
    have harg := congrArg (fun w : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B =>
      mfderiv 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) eb (L 0) w) hdl
    have hzero := congrArg (fun z : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B =>
      mfderiv 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) eb z (L v)) L.map_zero
    have hdb : mfderiv 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) eb 0 (L v) = L v :=
      congrArg (fun D : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B →L[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B => D (L v)) hb.mfderiv
    exact hright.trans (harg.trans (hzero.trans hdb))
  exact hl.symm.trans (ht.trans hr)

theorem linearLift_eq_nativeDifferential (f : A.toOver ⟶ B.toOver) [IsMonHom f] :
    Maps.IntrinsicLinearMaps.linearLift f =
      (mfderiv 𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) 𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) 1).toLinearMap := by
  apply LinearMap.ext
  intro v
  exact (linearLift_real_derivative f v).symm.trans (ComplexPoints.Analytic.IntrinsicDerivativeScalars.real_mfderiv_nativeScheme_map_apply f 1 v)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LiftDifferential.IntrinsicLinearMaps
