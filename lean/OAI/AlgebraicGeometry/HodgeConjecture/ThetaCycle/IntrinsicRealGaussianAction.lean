import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicGaussianCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicArchimedeanLift

/-! # Intrinsic Real Gaussian Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicRealGaussianAction.CM

noncomputable section

/-! The actual normalized native real splittings, transported to the
standard character, and their exact Gaussian determinant coefficients. -/

open scoped _root_.NumberField
open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural
open OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians OAI.RepresentationTheory.Theta.Adelic.LocalPositionInclusion
open OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction OAI.RepresentationTheory.Theta.Adelic.DataTheta

local instance nativeRealGaussianMeasurable (F : Type) [Field F] [NumberField F]
    (v : InfinitePlace F) : MeasurableSpace (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := borel _
local instance nativeRealGaussianBorel (F : Type) [Field F] [NumberField F]
    (v : InfinitePlace F) : BorelSpace (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := ⟨rfl⟩
local instance nativeRealGaussianSecondCountable (F : Type) [Field F] [NumberField F]
    (v : InfinitePlace F) : SecondCountableTopology (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := by
  have : CharZero (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionCharZero F (.inl v)
  exact RepresentationTheory.Weil.UnitarySplitting.TestSpaceAnalysis.Construction.localField_secondCountable _ (RepresentationTheory.Weil.AdelicSplitting.LocalKernel.Construction.completion_nondiscrete F (.inl v))

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W) (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H W)
  (hd : d ≠ 0) (C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
  (D : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H W hd C P) (hC : C.ψ = FieldAdelicCharacter.CM.fieldAdelicCharacter F)

def nativeStandardRealSplitting (v : Fin A.places) :
    RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (A.enumerate v))) →ₜ*
      RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.LocalCover ℝ (3 * m) (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) :=
  (RealFieldGaussian.CM.realFieldStandardCover (A.real v) (A.real_continuous v) (A.real_inverse_continuous v)
    (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inl (A.enumerate v))) (IntrinsicGaussianCoordinates.CM.native_real_trace_character A C hC v)).comp
      (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUSplitting F H W hd C P D (.inl (A.enumerate v)))

theorem native_standard_real_splitting_metaplectic (v : Fin A.places)
    (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (A.enumerate v)))) :
    nativeStandardRealSplitting A P hd C D hC v g ∈ RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticSubgroup ℝ (3 * m) (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) :=
  BallPerfect.CM.perfect_oscillator_lift_mem_metaplectic (ArchimedeanUnitaryPerfect.CM.native_enumerated_real_unitary_perfect A v)
    (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) (nativeStandardRealSplitting A P hd C D hC v).toMonoidHom g

theorem native_local_projection_real (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (v : Fin A.places) :
    RepresentationTheory.Weil.Local.FieldFourier.Construction.fieldSymplecticMap (A.real v) (3 * m)
      (RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localProjection (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl (A.enumerate v))) (3 * m)
        (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inl (A.enumerate v)))
        (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUSplitting F H W hd C P D (.inl (A.enumerate v)) (g (A.enumerate v)))) =
      RepresentationTheory.Theta.Adelic.RealSymplecticAction.localRealSymplectic A P g v := by
  change RepresentationTheory.Weil.Local.FieldFourier.Construction.fieldSymplecticMap (A.real v) (3 * m)
    (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.projectionAt F (3 * m) C.ψ (.inl (A.enumerate v))
      (D.atPlace (.inl (A.enumerate v)) (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUToPair F H W (.inl (A.enumerate v)) (g (A.enumerate v))))) = _
  rw [D.covers]
  rfl

theorem native_standard_real_splitting_projection (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (v : Fin A.places) :
    RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localProjection ℝ (3 * m) (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1)
      (nativeStandardRealSplitting A P hd C D hC v (g (A.enumerate v))) = RepresentationTheory.Theta.Adelic.RealSymplecticAction.localRealSymplectic A P g v := by
  exact (RealFieldGaussian.CM.real_field_standard_cover_projection (A.real v) (A.real_continuous v) (A.real_inverse_continuous v)
    (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inl (A.enumerate v))) (IntrinsicGaussianCoordinates.CM.native_real_trace_character A C hC v)
    (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUSplitting F H W hd C P D (.inl (A.enumerate v)) (g (A.enumerate v)))).trans
      (native_local_projection_real A P hd C D g v)

def nativeLocalGaussianCoefficient (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (v : Fin A.places) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) : ℂ :=
  (RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localOperator (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl (A.enumerate v))) (3 * m)
    (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inl (A.enumerate v)))
    (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUSplitting F H W hd C P D (.inl (A.enumerate v)) (g (A.enumerate v)))
    (RepresentationTheory.Theta.Adelic.GeometricGaussians.nativeGaussian A P v z 0)).val 0

theorem native_standard_real_gaussian_coefficient (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (v : Fin A.places) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    RealGaussianCoefficient.CM.realGaussianCoefficient (nativeStandardRealSplitting A P hd C D hC v (g (A.enumerate v)))
      (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z) = nativeLocalGaussianCoefficient A P hd C D g v z := by
  have hz : RepresentationTheory.Theta.Adelic.GeometricGaussians.nativeGaussian A P v z 0 = RealFieldGaussian.CM.realFieldGaussian (A.real v) (A.real_continuous v)
      (A.real_inverse_continuous v) (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z) 0 := by
    simpa only [RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localJacobiParameter, Matrix.mulVec_zero] using IntrinsicGaussianCoordinates.CM.native_gaussian_real_field A P v z 0
  unfold nativeLocalGaussianCoefficient
  rw [hz]
  exact RealFieldGaussian.CM.real_field_gaussian_coefficient (A.real v) (A.real_continuous v) (A.real_inverse_continuous v)
    (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inl (A.enumerate v))) (IntrinsicGaussianCoordinates.CM.native_real_trace_character A C hC v)
    (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUSplitting F H W hd C P D (.inl (A.enumerate v)) (g (A.enumerate v))) (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z)

include hC in
theorem native_local_gaussian_coefficient_square (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (v : Fin A.places) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    nativeLocalGaussianCoefficient A P hd C D g v z ^ 2 *
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks (OscillatorPhaseOrder.CM.swapSymplecticPhase (RepresentationTheory.Theta.Adelic.RealSymplecticAction.localRealSymplectic A P g v))).complexify.denominator
        (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z).matrix).det = 1 := by
  have h := MetaplecticGaussianCoefficient.CM.metaplectic_gaussian_coefficient_square (OscillatorPhaseOrder.CM.swapSymplecticPhase (RepresentationTheory.Theta.Adelic.RealSymplecticAction.localRealSymplectic A P g v))
    (nativeStandardRealSplitting A P hd C D hC v (g (A.enumerate v)))
    (native_standard_real_splitting_metaplectic A P hd C D hC v (g (A.enumerate v)))
    ((native_standard_real_splitting_projection A P hd C D hC g v).trans
      (OscillatorPhaseOrder.CM.swap_symplectic_phase_involutive (RepresentationTheory.Theta.Adelic.RealSymplecticAction.localRealSymplectic A P g v)).symm)
    (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z)
  rwa [native_standard_real_gaussian_coefficient] at h

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicRealGaussianAction.CM
