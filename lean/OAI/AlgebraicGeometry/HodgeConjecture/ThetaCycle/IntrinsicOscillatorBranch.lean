import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicGaussianCocycle
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.GaussianCoefficientContinuity
import OAI.RepresentationTheory.Theta.Adelic.LocalPeriodHolomorphic
import OAI.RepresentationTheory.Theta.Adelic.GeometricAutomorphy
import OAI.RepresentationTheory.Theta.Adelic.PerfectCocycleComparison

/-! # Intrinsic Oscillator Branch -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicOscillatorBranch.CM

noncomputable section

/-! The actual Gaussian-operator branch equals the independently
constructed geometric branch, by continuity and perfectness. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.BallNatural
open OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction OAI.RepresentationTheory.Theta.Adelic.LocalPositionInclusion
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.GeometricGroup OAI.RepresentationTheory.Theta.Adelic.GeometricAutomorphy
open OAI.RepresentationTheory.Theta.Adelic.BallHolomorphicSquare OAI.RepresentationTheory.Theta.Adelic.GeometricHalfFrame
open OAI.RepresentationTheory.Theta.Adelic.BallNatural.LineLift

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W) (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H W)
  (hd : d ≠ 0) (C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
  (D : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H W hd C P) (hC : C.ψ = FieldAdelicCharacter.CM.fieldAdelicCharacter F)

include hC in
theorem native_local_gaussian_coefficient_continuous (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (v : Fin A.places) :
    Continuous (IntrinsicRealGaussianAction.CM.nativeLocalGaussianCoefficient A P hd C D g v) := by
  have hZ : Continuous (fun z => (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z).matrix) :=
    RepresentationTheory.Theta.Adelic.BallHolomorphicSquare.ball_holomorphic_continuous _
      (RepresentationTheory.Theta.Adelic.LocalPeriodHolomorphic.localSiegelPeriod_holomorphic A P v)
  have hT : Continuous (fun z =>
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks (OscillatorPhaseOrder.CM.swapSymplecticPhase (RepresentationTheory.Theta.Adelic.RealSymplecticAction.localRealSymplectic A P g v))).transformSiegel
        (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z)).matrix) := by
    change Continuous (fun z => ((IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).transformSiegel
      (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z)).matrix)
    simp only [← IntrinsicJacobi.CM.native_local_period_covariance A P g v]
    exact hZ.comp (by fun_prop)
  have h := GaussianCoefficientContinuity.CM.real_gaussian_coefficient_continuous
    (OscillatorPhaseOrder.CM.swapSymplecticPhase (RepresentationTheory.Theta.Adelic.RealSymplecticAction.localRealSymplectic A P g v))
    (IntrinsicRealGaussianAction.CM.nativeStandardRealSplitting A P hd C D hC v (g (A.enumerate v)))
    ((IntrinsicRealGaussianAction.CM.native_standard_real_splitting_projection A P hd C D hC g v).trans
      (OscillatorPhaseOrder.CM.swap_symplectic_phase_involutive (RepresentationTheory.Theta.Adelic.RealSymplecticAction.localRealSymplectic A P g v)).symm)
    (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v) hZ hT
  apply h.congr
  intro z
  exact IntrinsicRealGaussianAction.CM.native_standard_real_gaussian_coefficient A P hd C D hC g v z

include hC in
theorem native_oscillator_factor_ball_continuous (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) :
    Continuous (RepresentationTheory.Theta.Adelic.DataTheta.oscillatorFactor (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) P hd C D g) := by
  change Continuous (fun z => RepresentationTheory.Theta.Adelic.DataTheta.oscillatorFactor (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) P hd C D g z)
  simp only [IntrinsicGaussianCocycle.CM.native_oscillator_factor_product]
  exact (continuous_finsetProd _ (fun v _ =>
    native_local_gaussian_coefficient_continuous A P hd C D hC g v)).inv₀
      (fun z => Finset.prod_ne_zero_iff.mpr (fun v _ =>
        IntrinsicGaussianCocycle.CM.native_local_gaussian_coefficient_ne_zero A P hd C D hC g v z))

include hC in
theorem native_oscillator_factor_eq_geometric :
    RepresentationTheory.Theta.Adelic.DataTheta.oscillatorFactor (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) P hd C D = RepresentationTheory.Theta.Adelic.GeometricAutomorphy.geometricFactor A P := by
  let : MulAction (RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) RepresentationTheory.Theta.Adelic.BallNatural.Ball :=
    MulAction.compHom RepresentationTheory.Theta.Adelic.BallNatural.Ball (RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom A).toMonoidHom
  let : ContractibleSpace RepresentationTheory.Theta.Adelic.BallNatural.Ball :=
    RepresentationTheory.Theta.Adelic.BallHolomorphicSquare.Root.ball_domain_starConvex.contractibleSpace
      RepresentationTheory.Theta.Adelic.BallHolomorphicSquare.Root.ball_domain_nonempty
  let z₀ : RepresentationTheory.Theta.Adelic.BallNatural.Ball := ⟨0, by change Complex.normSq 0 + Complex.normSq 0 < 1; norm_num⟩
  exact RepresentationTheory.Theta.Adelic.PerfectCocycleComparison.perfect_square_cocycles_eq
    (ArchimedeanUnitaryPerfect.CM.native_archimedean_unitary_perfect A) z₀
    (RepresentationTheory.Theta.Adelic.DataTheta.oscillatorFactor (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) P hd C D) (RepresentationTheory.Theta.Adelic.GeometricAutomorphy.geometricFactor A P)
    (native_oscillator_factor_ball_continuous A P hd C D hC)
    (RepresentationTheory.Theta.Adelic.BallHolomorphicSquare.continuous_fixed_left _ (RepresentationTheory.Theta.Adelic.GeometricAutomorphy.geometricFactor_continuous A P))
    (fun g z => (IntrinsicGaussianCocycle.CM.native_oscillator_factor_square A P hd C D hC g z).1)
    (RepresentationTheory.Theta.Adelic.GeometricAutomorphy.geometricFactor_nonzero A P)
    (fun g z => (IntrinsicGaussianCocycle.CM.native_oscillator_factor_square A P hd C D hC g z).2.trans
      (RepresentationTheory.Theta.Adelic.GeometricAutomorphy.geometricFactor_square A P g z).symm)
    (IntrinsicGaussianCocycle.CM.native_oscillator_factor_mul A P hd C D hC)
    (RepresentationTheory.Theta.Adelic.GeometricAutomorphy.geometricFactor_mul A P) (IntrinsicGaussianCocycle.CM.native_oscillator_factor_one A P hd C D)
    (RepresentationTheory.Theta.Adelic.GeometricAutomorphy.geometricFactor_one A P)

include hC in
theorem native_oscillator_factor_continuous :
    Continuous (fun p : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H × RepresentationTheory.Theta.Adelic.BallNatural.Ball =>
      RepresentationTheory.Theta.Adelic.DataTheta.oscillatorFactor (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) P hd C D p.1 p.2) := by
  rw [native_oscillator_factor_eq_geometric A P hd C D hC]
  exact RepresentationTheory.Theta.Adelic.GeometricAutomorphy.geometricFactor_continuous A P

include hC in
theorem native_oscillator_factor_holomorphic (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) :
    RepresentationTheory.Theta.Adelic.BallGeometryData.BallHolomorphic (RepresentationTheory.Theta.Adelic.DataTheta.oscillatorFactor (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) P hd C D g) := by
  rw [native_oscillator_factor_eq_geometric A P hd C D hC]
  exact RepresentationTheory.Theta.Adelic.GeometricAutomorphy.Holomorphic.geometricFactor_holomorphic A P g

include hC in
theorem native_oscillator_factor_natural (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (a : ℂ) :
    (RepresentationTheory.Theta.Adelic.DataTheta.oscillatorFactor (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) P hd C D g z * RepresentationTheory.Theta.Adelic.GeometricHalfFrame.geometricHalfFrame A P z /
      RepresentationTheory.Theta.Adelic.GeometricHalfFrame.geometricHalfFrame A P (RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom A g • z)) * a =
      (RepresentationTheory.Theta.Adelic.BallNatural.LineLift.naturalLineLift m (RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom A g) (z, a)).2 := by
  rw [native_oscillator_factor_eq_geometric A P hd C D hC]
  exact RepresentationTheory.Theta.Adelic.GeometricAutomorphy.geometricFactor_natural A P g z a

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicOscillatorBranch.CM
