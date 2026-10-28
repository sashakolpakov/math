import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RiemannForm
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-! # Period Riemann Pairing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.PeriodRiemannPairing

noncomputable section

/-! The complexified original Chern pairing is expressed through the
actual positive Riemann form and the two native period projections. -/

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped TensorProduct

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (hL : L.IsAmple)
local instance : AlgebraicGeometry.IsIntegral A.toOver.left := A.variety.property

def complexChernForm : LinearMap.BilinForm ℂ (ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) :=
  LinearMap.BilinForm.baseChange ℂ (Intrinsic.ChernPairing.nativeChernForm A L)

theorem nativeRiemannForm_period_difference (v w : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    Intrinsic.RiemannForm.nativeRiemannForm A L hL v.val w.val - Intrinsic.RiemannForm.nativeRiemannForm A L hL w.val v.val =
      2 * Complex.I * (Intrinsic.ChernPairing.nativeChernForm A L v w : ℂ) := by
  rw [Intrinsic.RiemannForm.nativeRiemannForm_symmetry A L hL v.val w.val]
  have hp := Intrinsic.RiemannForm.nativeRiemannForm_period A L hL v w
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
  · simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, hp]
    norm_num [Complex.mul_re, Complex.mul_im]
    ring

theorem complexChernForm_riemann (u v : ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) :
    2 * Complex.I * complexChernForm A L u v =
      Intrinsic.RiemannForm.nativeRiemannForm A L hL
        (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (ComplexMultiplication.WeightOne.CM.coefficientConjugation (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u))
        (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A v) -
      Intrinsic.RiemannForm.nativeRiemannForm A L hL
        (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (ComplexMultiplication.WeightOne.CM.coefficientConjugation (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) v))
        (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A u) := by
  let H : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ⋆[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℂ] ℂ := Intrinsic.RiemannForm.nativeRiemannForm A L hL
  change 2 * Complex.I * complexChernForm A L u v =
    H (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (ComplexMultiplication.WeightOne.CM.coefficientConjugation (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u))
      (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A v) -
    H (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (ComplexMultiplication.WeightOne.CM.coefficientConjugation (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) v))
      (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A u)
  induction u using TensorProduct.inductionOn with
  | add u w hu hw =>
      simp only [map_add, LinearMap.add_apply, mul_add, hu, hw]
      ring
  | tmul z x =>
      induction v using TensorProduct.inductionOn with
      | add v w hv hw =>
          simp only [map_add, LinearMap.add_apply, mul_add, hv, hw]
          ring
      | tmul t y =>
          rw [complexChernForm, LinearMap.BilinForm.baseChange_tmul]
          simp only [ComplexMultiplication.WeightOne.CM.coefficientConjugation_tmul, Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection_tmul,
            map_smulₛₗ, RingHom.id_apply, starRingEnd_apply, star_star,
            LinearMap.smul_apply, smul_eq_mul, Rat.smul_def]
          have h := nativeRiemannForm_period_difference A L hL x y
          change _ = t * (z * Intrinsic.RiemannForm.nativeRiemannForm A L hL x.val y.val) -
            z * (t * Intrinsic.RiemannForm.nativeRiemannForm A L hL y.val x.val)
          calc
            _ = z * t * (Intrinsic.RiemannForm.nativeRiemannForm A L hL x.val y.val -
                Intrinsic.RiemannForm.nativeRiemannForm A L hL y.val x.val) := by rw [h]; ring
            _ = _ := by ring

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.PeriodRiemannPairing
