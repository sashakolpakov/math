import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicJacobi
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicRealGaussianAction

/-! # Intrinsic Gaussian Cocycle -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicGaussianCocycle.CM

noncomputable section

section

/-! The independently evaluated native archimedean oscillator factor
has exactly the global geometric Siegel denominator as its square. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.BallNatural
open OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta

local instance nativeOscillatorSquareMeasurable (F : Type) [Field F] [NumberField F]
    (v : NumberField.InfinitePlace F) : MeasurableSpace (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := borel _
local instance nativeOscillatorSquareBorel (F : Type) [Field F] [NumberField F]
    (v : NumberField.InfinitePlace F) : BorelSpace (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := ⟨rfl⟩

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W) (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H W)
  (hd : d ≠ 0) (C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
  (D : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H W hd C P) (hC : C.ψ = FieldAdelicCharacter.CM.fieldAdelicCharacter F)

include hC in
theorem native_local_gaussian_coefficient_ne_zero (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (v : Fin A.places) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    IntrinsicRealGaussianAction.CM.nativeLocalGaussianCoefficient A P hd C D g v z ≠ 0 := by
  intro hz
  have h := IntrinsicRealGaussianAction.CM.native_local_gaussian_coefficient_square A P hd C D hC g v z
  rw [hz, zero_pow (by decide : 2 ≠ 0), zero_mul] at h
  exact zero_ne_one h

theorem native_oscillator_factor_product (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    RepresentationTheory.Theta.Adelic.DataTheta.oscillatorFactor (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) P hd C D g z =
      (∏ v, IntrinsicRealGaussianAction.CM.nativeLocalGaussianCoefficient A P hd C D g v z)⁻¹ := by
  unfold RepresentationTheory.Theta.Adelic.DataTheta.oscillatorFactor
  apply congrArg (fun c : ℂ => c⁻¹)
  apply Finset.prod_congr rfl
  intro v _
  change (RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localOperator _ _ _
    (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUSplitting F H W hd C P D (.inl (A.enumerate v)) (g (A.enumerate v)))
      (RepresentationTheory.Theta.Adelic.GeometricGaussians.gaussianFamily A P z 0 (A.enumerate v))).val 0 = _
  rw [RepresentationTheory.Theta.Adelic.GeometricGaussians.gaussianFamily_enumerate]
  rfl

include hC in
theorem native_oscillator_factor_square (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    RepresentationTheory.Theta.Adelic.DataTheta.oscillatorFactor (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) P hd C D g z ≠ 0 ∧
      RepresentationTheory.Theta.Adelic.DataTheta.oscillatorFactor (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) P hd C D g z ^ 2 =
        ((RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).complexify.denominator (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z).matrix).det := by
  have hp : (∏ v, IntrinsicRealGaussianAction.CM.nativeLocalGaussianCoefficient A P hd C D g v z) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun v _ => native_local_gaussian_coefficient_ne_zero A P hd C D hC g v z)
  have hs : (∏ v, IntrinsicRealGaussianAction.CM.nativeLocalGaussianCoefficient A P hd C D g v z) ^ 2 *
      ((RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).complexify.denominator (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z).matrix).det = 1 := by
    rw [IntrinsicJacobi.CM.native_global_denominator_det_product, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun v _ => IntrinsicRealGaussianAction.CM.native_local_gaussian_coefficient_square A P hd C D hC g v z)
  rw [native_oscillator_factor_product]
  refine ⟨inv_ne_zero hp, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 hp)
  rw [hs, ← mul_pow, mul_inv_cancel₀ hp, one_pow]

end

/-! Actual zero-Jacobi Gaussian covariance and the resulting oscillator
cocycle, before comparison with the geometric determinant branch. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.BallNatural
open OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction OAI.RepresentationTheory.Theta.Adelic.LocalPositionInclusion
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.GeometricGroup

local instance nativeGaussianCocycleMeasurable (F : Type) [Field F] [NumberField F]
    (v : NumberField.InfinitePlace F) : MeasurableSpace (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := borel _
local instance nativeGaussianCocycleBorel (F : Type) [Field F] [NumberField F]
    (v : NumberField.InfinitePlace F) : BorelSpace (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := ⟨rfl⟩
local instance nativeGaussianCocycleSecondCountable (F : Type) [Field F] [NumberField F]
    (v : NumberField.InfinitePlace F) : SecondCountableTopology (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := by
  have : CharZero (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionCharZero F (.inl v)
  exact RepresentationTheory.Weil.UnitarySplitting.TestSpaceAnalysis.Construction.localField_secondCountable _ (RepresentationTheory.Weil.AdelicSplitting.LocalKernel.Construction.completion_nondiscrete F (.inl v))

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W) (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H W)
  (hd : d ≠ 0) (C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
  (D : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H W hd C P) (hC : C.ψ = FieldAdelicCharacter.CM.fieldAdelicCharacter F)

include hC in
theorem native_local_gaussian_zero_covariance (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (v : Fin A.places) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localOperator (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl (A.enumerate v))) (3 * m)
      (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inl (A.enumerate v)))
      (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUSplitting F H W hd C P D (.inl (A.enumerate v)) (g (A.enumerate v))) (RepresentationTheory.Theta.Adelic.GeometricGaussians.nativeGaussian A P v z 0) =
    IntrinsicRealGaussianAction.CM.nativeLocalGaussianCoefficient A P hd C D g v z • RepresentationTheory.Theta.Adelic.GeometricGaussians.nativeGaussian A P v (RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom A g • z) 0 := by
  let a := RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUSplitting F H W hd C P D (.inl (A.enumerate v)) (g (A.enumerate v))
  have hz (w : RepresentationTheory.Theta.Adelic.BallNatural.Ball) : RepresentationTheory.Theta.Adelic.GeometricGaussians.nativeGaussian A P v w 0 = RealFieldGaussian.CM.realFieldGaussian (A.real v) (A.real_continuous v)
      (A.real_inverse_continuous v) (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v w) 0 := by
    simpa only [RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localJacobiParameter, Matrix.mulVec_zero] using IntrinsicGaussianCoordinates.CM.native_gaussian_real_field A P v w 0
  have hc : RealFieldGaussian.CM.realFieldGaussianCoefficient (A.real v) (A.real_continuous v) (A.real_inverse_continuous v)
      (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inl (A.enumerate v))) a (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z) =
      IntrinsicRealGaussianAction.CM.nativeLocalGaussianCoefficient A P hd C D g v z := by
    unfold IntrinsicRealGaussianAction.CM.nativeLocalGaussianCoefficient
    rw [hz]
    rfl
  have h := RealFieldGaussian.CM.real_field_gaussian_covariance (A.real v) (A.real_continuous v) (A.real_inverse_continuous v)
    (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inl (A.enumerate v))) (IntrinsicGaussianCoordinates.CM.native_real_trace_character A C hC v)
    a (OscillatorPhaseOrder.CM.swapSymplecticPhase (RepresentationTheory.Theta.Adelic.RealSymplecticAction.localRealSymplectic A P g v))
    ((IntrinsicRealGaussianAction.CM.native_local_projection_real A P hd C D g v).trans
      (OscillatorPhaseOrder.CM.swap_symplectic_phase_involutive (RepresentationTheory.Theta.Adelic.RealSymplecticAction.localRealSymplectic A P g v)).symm)
    (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z) 0
  rw [hz, hz, IntrinsicJacobi.CM.native_local_period_covariance]
  simpa only [hc, map_zero, _root_.zero_apply, neg_zero, Complex.exp_zero, mul_one] using! h

include hC in
theorem native_local_gaussian_coefficient_mul (g h : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (v : Fin A.places) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    IntrinsicRealGaussianAction.CM.nativeLocalGaussianCoefficient A P hd C D (g * h) v z =
      IntrinsicRealGaussianAction.CM.nativeLocalGaussianCoefficient A P hd C D g v (RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom A h • z) *
        IntrinsicRealGaussianAction.CM.nativeLocalGaussianCoefficient A P hd C D h v z := by
  let T := (RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localOperator (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl (A.enumerate v))) (3 * m)
    (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inl (A.enumerate v)))).comp
      (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUSplitting F H W hd C P D (.inl (A.enumerate v))).toMonoidHom
  change (T (g (A.enumerate v) * h (A.enumerate v)) (RepresentationTheory.Theta.Adelic.GeometricGaussians.nativeGaussian A P v z 0)).val 0 = _
  rw [map_mul, LinearEquiv.mul_apply]
  have hh := native_local_gaussian_zero_covariance A P hd C D hC h v z
  change T (h (A.enumerate v)) (RepresentationTheory.Theta.Adelic.GeometricGaussians.nativeGaussian A P v z 0) = _ at hh
  rw [hh, map_smul]
  change IntrinsicRealGaussianAction.CM.nativeLocalGaussianCoefficient A P hd C D h v z *
    IntrinsicRealGaussianAction.CM.nativeLocalGaussianCoefficient A P hd C D g v (RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom A h • z) = _
  exact mul_comm _ _

theorem native_local_gaussian_coefficient_one (v : Fin A.places) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    IntrinsicRealGaussianAction.CM.nativeLocalGaussianCoefficient A P hd C D 1 v z = 1 := by
  unfold IntrinsicRealGaussianAction.CM.nativeLocalGaussianCoefficient
  simp only [Pi.one_apply, map_one]
  change (RepresentationTheory.Theta.Adelic.GeometricGaussians.nativeGaussian A P v z 0).val 0 = 1
  exact RepresentationTheory.Theta.Adelic.GeometricGaussians.nativeGaussian_at_zero A P v z 0

include hC in
theorem native_oscillator_factor_mul (g h : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    RepresentationTheory.Theta.Adelic.DataTheta.oscillatorFactor (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) P hd C D (g * h) z =
      RepresentationTheory.Theta.Adelic.DataTheta.oscillatorFactor (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) P hd C D g (RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom A h • z) *
        RepresentationTheory.Theta.Adelic.DataTheta.oscillatorFactor (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) P hd C D h z := by
  simp only [native_oscillator_factor_product, native_local_gaussian_coefficient_mul A P hd C D hC,
    Finset.prod_mul_distrib, mul_inv]

theorem native_oscillator_factor_one (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    RepresentationTheory.Theta.Adelic.DataTheta.oscillatorFactor (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) P hd C D 1 z = 1 := by
  simp only [native_oscillator_factor_product, native_local_gaussian_coefficient_one,
    Finset.prod_const_one, inv_one]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicGaussianCocycle.CM
