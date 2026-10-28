import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineGroupAction
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalGeometricLevel

/-! # Single Line Level -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineLevel.CM

noncomputable section

/-! A single actual principal level preserves the fixed original input
of a source line in the full native tensor law, at every Taylor order. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun k v => d k (places.representative v)))
  (hμ : ∀ k, d k (places.representative places.distinguished) = true) (j : Fin 2)
  (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j)) (hL : L.coordinates.a = Q.a j ∧ L.coordinates.delta = Q.delta)

def SingleSourceThetaCovariant (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places))
    (N : ℕ) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel N g) : Prop :=
  ∀ (z : B.Domain) (a : ℕ) (u : Fin a → RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) → ℂ),
    RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor (SingleLineComponents.CM.directSingleLineComparison K Q hμ j)
      (SingleLineComparison.CM.directSingleNativeFiniteInput K Q hμ j L.coordinates hL φ) a
      (SourceIntrinsicBall.CM.sourceNativeBallPoint K B (BallLineAction.CM.ballPrincipalAction K B g hg.1 z))
      (fun i => RepresentationTheory.Theta.Adelic.BallGeometryData.dualFrameChange (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j)
        (SingleLineGroupAction.CM.singleSourceArchimedeanElement K Q N g hg) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) (u i)) =
      ((BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2) *
        RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor (SingleLineComponents.CM.directSingleLineComparison K Q hμ j)
          (SingleLineComparison.CM.directSingleNativeFiniteInput K Q hμ j L.coordinates hL φ) a (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) u

theorem native_covariance_for_single_source (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places))
    (N : ℕ) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel N g)
    (h : IntrinsicFixedCovariance.CM.NativeGeometricThetaCovariant (SingleLineComponents.CM.directSingleLineFrames K Q j)
      (SingleLineGroupAction.CM.singleSourceArchimedeanElement K Q N g hg) (SingleLineComparison.CM.directSingleNativeFiniteInput K Q hμ j L.coordinates hL φ)) :
    SingleSourceThetaCovariant K d Q hμ j L hL φ N g hg := by
  intro z a u
  have hc := h (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) a u
  have hp := SingleLineGroupAction.CM.direct_single_principal_native_ball_action K Q hμ j N g hg z
  have hf := SingleLineGroupAction.CM.direct_single_native_half_factor K Q hμ j N g hg z
  have he := congrArg (fun w =>
    RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor (SingleLineComponents.CM.directSingleLineComparison K Q hμ j)
      (SingleLineComparison.CM.directSingleNativeFiniteInput K Q hμ j L.coordinates hL φ) a w
      (fun i => RepresentationTheory.Theta.Adelic.BallGeometryData.dualFrameChange (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j)
        (SingleLineGroupAction.CM.singleSourceArchimedeanElement K Q N g hg) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) (u i))) hp.symm
  exact he.trans (hc.trans (congrArg (fun c => c *
    RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor (SingleLineComponents.CM.directSingleLineComparison K Q hμ j)
      (SingleLineComparison.CM.directSingleNativeFiniteInput K Q hμ j L.coordinates hL φ) a (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) u) hf))

theorem exists_single_source_theta_level (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places)) :
    ∃ M : ℕ, 0 < M ∧ ∀ N : ℕ, M ∣ N →
      ∀ (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel N g),
        SingleSourceThetaCovariant K d Q hμ j L hL φ N g hg := by
  let f := SingleLineComparison.CM.directSingleNativeFiniteInput K Q hμ j L.coordinates hL φ
  have hlevel := PrincipalGeometricLevel.CM.exists_principal_all_geometric_theta_level K Q.delta Q.delta_imaginary
    Q.delta_ne_zero B 1 (by decide)
    (SingleLineArithmetic.CM.directSingleLineSkewUnit K Q.delta Q.delta_imaginary Q.delta_ne_zero (Q.a j)
      (BallArithmetic.CM.direct_source_a_fixed K Q j) (BallArithmetic.CM.direct_source_a_ne_zero K Q j))
    (SingleLineArithmetic.CM.direct_single_line_skew_conjugate_transpose K Q.delta Q.delta_imaginary Q.delta_ne_zero
      (Q.a j) (BallArithmetic.CM.direct_source_a_fixed K Q j) (BallArithmetic.CM.direct_source_a_ne_zero K Q j))
    (SingleLineComponents.CM.directSingleLineFrames K Q j) {f}
  refine ⟨hlevel.choose, hlevel.choose_spec.1, ?_⟩
  intro N hN g hg
  exact native_covariance_for_single_source K d Q hμ j L hL φ N g hg
    ((hlevel.choose_spec.2 N hN).2 g hg f (Finset.mem_singleton_self f))

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineLevel.CM
