import OAI.RepresentationTheory.Theta.Adelic.DualFrameJacobi
import OAI.RepresentationTheory.Theta.Adelic.GeometricAutomorphy
import OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians

/-! # Geometric Tensor Covariance -/

namespace OAI.RepresentationTheory.Theta.Adelic.GeometricTensorCovariance

noncomputable section

/-! Completed tensor covariance in the natural geometric half-line and
Hodge frames, using their independently proved transition identities. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallNatural.Factors OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates OAI.RepresentationTheory.Theta.Adelic.GeometricGroup OAI.RepresentationTheory.Theta.Adelic.GeometricHalfFrame
open OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction OAI.RepresentationTheory.Theta.Adelic.DualFrameJacobi OAI.RepresentationTheory.Theta.Adelic.GeometricAutomorphy

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem geometric_half_rescale (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball) (c : ℂ) :
    (GeometricHalfFrame.geometricHalfFrame A P (GeometricGroup.geometricBallHom A g • z))⁻¹ * (GeometricAutomorphy.geometricFactor A P g z * c) =
      BallNatural.Factors.naturalHalfFactor m (GeometricGroup.geometricBallHom A g) z * ((GeometricHalfFrame.geometricHalfFrame A P z)⁻¹ * c) := by
  rw [GeometricAutomorphy.geometricFactor]
  field_simp [GeometricHalfFrame.geometricHalfFrame_nonzero A P (GeometricGroup.geometricBallHom A g • z)]

theorem geometricTensor_covariance_of_completed
    (f fnew : FiniteSchwartz.finiteSchwartz F (3 * m)) (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball) (a : ℕ)
    (ht : ∀ v : Fin a → BallGeometryData.FrameIndex A → ℂ,
      DataTheta.completedTensor (GeometricGaussians.constructedComparison A P) fnew a
        (PeriodCoordinates.geometricPeriod A P (GeometricGroup.geometricBallHom A g • z)).matrix
        (fun i => (RealSymplecticAction.realSymplecticBlocks A P g).jacobiChange (PeriodCoordinates.geometricPeriod A P z) (v i)) =
      GeometricAutomorphy.geometricFactor A P g z *
        DataTheta.completedTensor (GeometricGaussians.constructedComparison A P) f a (PeriodCoordinates.geometricPeriod A P z).matrix v)
    (v : Fin a → BallGeometryData.FrameIndex A → ℂ) :
    DataTheta.geometricTensor (GeometricGaussians.constructedComparison A P) fnew a (GeometricGroup.geometricBallHom A g • z)
      (fun i => BallGeometryData.dualFrameChange A g z (v i)) =
      BallNatural.Factors.naturalHalfFactor m (GeometricGroup.geometricBallHom A g) z *
        DataTheta.geometricTensor (GeometricGaussians.constructedComparison A P) f a z v := by
  change (GeometricHalfFrame.geometricHalfFrame A P (GeometricGroup.geometricBallHom A g • z))⁻¹ *
    (DataTheta.completedTensor (GeometricGaussians.constructedComparison A P) fnew a
      (PeriodCoordinates.geometricPeriod A P (GeometricGroup.geometricBallHom A g • z)).matrix)
      (fun i => ((PeriodCoordinates.geometricPositionUnit A P (GeometricGroup.geometricBallHom A g • z)).invᵀ).mulVec
        (BallGeometryData.dualFrameChange A g z (v i))) =
    BallNatural.Factors.naturalHalfFactor m (GeometricGroup.geometricBallHom A g) z *
      ((GeometricHalfFrame.geometricHalfFrame A P z)⁻¹ *
        (DataTheta.completedTensor (GeometricGaussians.constructedComparison A P) f a (PeriodCoordinates.geometricPeriod A P z).matrix)
          (fun i => ((PeriodCoordinates.geometricPositionUnit A P z).invᵀ).mulVec (v i)))
  simp_rw [DualFrameJacobi.geometric_dual_frame_jacobi A P g z]
  rw [ht]
  exact geometric_half_rescale A P g z _

end

end OAI.RepresentationTheory.Theta.Adelic.GeometricTensorCovariance
