import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.PeriodRiemannPairing
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PolarizationFromPositiveForm

/-! # Period Polarization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodPolarization

noncomputable section

/-! The original ample Chern class polarizes the constructed native
period Hodge structure, with isotropy and positivity proved from its
actual positive Riemann form. -/

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (hL : L.IsAmple)

include hL

theorem complexChernForm_periodKernel_isotropic
    (u v : ComplexMultiplication.WeightOne.CM.Complexification (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A))
    (hu : u ∈ (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A).ker) (hv : v ∈ (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A).ker) :
    ReferenceFamily.Complex.PeriodRiemannPairing.complexChernForm A L u v = 0 := by
  have h := ReferenceFamily.Complex.PeriodRiemannPairing.complexChernForm_riemann A L hL u v
  let H : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ⋆[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℂ] ℂ := RiemannForm.nativeRiemannForm A L hL
  change 2 * Complex.I * ReferenceFamily.Complex.PeriodRiemannPairing.complexChernForm A L u v =
    H (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u)) (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A v) -
    H (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) v)) (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A u) at h
  have hz : 2 * Complex.I * ReferenceFamily.Complex.PeriodRiemannPairing.complexChernForm A L u v = 0 := by
    simpa only [LinearMap.mem_ker.mp hu, LinearMap.mem_ker.mp hv,
      map_zero, LinearMap.zero_apply, sub_zero] using h
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) Complex.I_ne_zero)

theorem complexChernForm_periodKernel_positive
    (u : ComplexMultiplication.WeightOne.CM.Complexification (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A))
    (hu : u ∈ (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A).ker) (hne : u ≠ 0) :
    0 < (Complex.I * ReferenceFamily.Complex.PeriodRiemannPairing.complexChernForm A L u
      (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u)).re := by
  have hp : PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u) ≠ 0 :=
    fun hz => hne (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.complexPeriodProjection_conjugate_joint_zero A u hu hz)
  have h := ReferenceFamily.Complex.PeriodRiemannPairing.complexChernForm_riemann A L hL u (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u)
  let H : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ⋆[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℂ] ℂ := RiemannForm.nativeRiemannForm A L hL
  change 2 * Complex.I * ReferenceFamily.Complex.PeriodRiemannPairing.complexChernForm A L u (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u) =
    H (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u))
      (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u)) -
    H (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)
      (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u))) (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A u) at h
  have he : 2 * Complex.I * ReferenceFamily.Complex.PeriodRiemannPairing.complexChernForm A L u
      (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u) =
      RiemannForm.nativeRiemannForm A L hL
        (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u))
        (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u)) := by
    change 2 * Complex.I * ReferenceFamily.Complex.PeriodRiemannPairing.complexChernForm A L u (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u) =
      H (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u))
        (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u))
    simpa only [ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive, LinearMap.mem_ker.mp hu,
      map_zero, LinearMap.zero_apply, sub_zero] using h
  have hpos := RiemannForm.nativeRiemannForm_positive A L hL _ hp
  have hre := congrArg Complex.re he
  have htwo : 0 < 2 * (Complex.I * ReferenceFamily.Complex.PeriodRiemannPairing.complexChernForm A L u
      (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u)).re := by
    have hh : (2 * Complex.I * ReferenceFamily.Complex.PeriodRiemannPairing.complexChernForm A L u
        (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u)).re =
        2 * (Complex.I * ReferenceFamily.Complex.PeriodRiemannPairing.complexChernForm A L u
          (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u)).re := by
      simp only [mul_assoc, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    exact hh ▸ (hre.symm ▸ hpos)
  linarith

def nativePeriodPolarization : ComplexMultiplication.CM.Polarization.WeightOnePolarization (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A) :=
  ComplexMultiplication.HodgeComparison.PolarizationFromPositiveForm.CM.Construction.weightOnePolarizationOfPositive (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A) (ChernPairing.nativeChernForm A L)
    (ChernPairing.nativeChernForm_alternating A L)
    (fun u hu v hv => complexChernForm_periodKernel_isotropic A L hL u v hu hv)
    (complexChernForm_periodKernel_positive A L hL)

theorem nativePeriodPolarization_form : (nativePeriodPolarization A L hL).form = ChernPairing.nativeChernForm A L := rfl

theorem complexChernForm_conjugateKernel_negative
    (u : ComplexMultiplication.WeightOne.CM.Complexification (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A))
    (hu : u ∈ IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.conjugatePeriodKernel A) (hne : u ≠ 0) :
    (Complex.I * ReferenceFamily.Complex.PeriodRiemannPairing.complexChernForm A L u (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u)).re < 0 := by
  have hp : PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A u ≠ 0 :=
    fun hz => hne (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.complexPeriodProjection_conjugate_joint_zero A u hz hu)
  have h := ReferenceFamily.Complex.PeriodRiemannPairing.complexChernForm_riemann A L hL u (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u)
  let H : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ⋆[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℂ] ℂ := RiemannForm.nativeRiemannForm A L hL
  change 2 * Complex.I * ReferenceFamily.Complex.PeriodRiemannPairing.complexChernForm A L u (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u) =
    H (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u))
      (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u)) -
    H (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)
      (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u))) (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A u) at h
  have hc : PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u) = 0 := hu
  have he : 2 * Complex.I * ReferenceFamily.Complex.PeriodRiemannPairing.complexChernForm A L u (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u) =
      -H (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A u) (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A u) := by
    simpa only [ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive, hc, map_zero, LinearMap.zero_apply, zero_sub] using h
  have hpos : 0 < (H (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A u) (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A u)).re :=
    RiemannForm.nativeRiemannForm_positive A L hL _ hp
  have hre := congrArg Complex.re he
  have hh : (2 * Complex.I * ReferenceFamily.Complex.PeriodRiemannPairing.complexChernForm A L u (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u)).re =
      2 * (Complex.I * ReferenceFamily.Complex.PeriodRiemannPairing.complexChernForm A L u (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u)).re := by
    simp only [mul_assoc, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  rw [hh, Complex.neg_re] at hre
  linarith

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodPolarization
