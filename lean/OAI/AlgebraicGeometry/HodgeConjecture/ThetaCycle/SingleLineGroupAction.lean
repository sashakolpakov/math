import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineGeometricTensor
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationGroupAction

/-! # Single Line Group Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineGroupAction.CM

noncomputable section

/-! The original principal ball action on one source line agrees with
its native geometric action in every CM-place component. -/

open scoped Classical _root_.NumberField _root_.Matrix Kronecker
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.TensorGeometricAction
open OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.GeometricGroup
open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallNatural.Factors _root_.Module

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true) (j : Fin 2)
  (N : ℕ) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel N g)

abbrev singleSourceArchimedeanElement :=
  RepresentationTheory.Theta.Adelic.RationalSU.rationalArchimedeanSU (maximalRealSubfield K)
    (CMGlobalFrames.CM.cmHermitianUnit K Q.delta Q.delta_imaginary B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B))
    (RationalBallUnitary.CM.rationalBallSU K Q.delta Q.delta_imaginary Q.delta_ne_zero B N g hg)

theorem direct_single_principal_native_ball_action (z : B.Domain) :
    RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) (singleSourceArchimedeanElement K Q N g hg) •
      SourceIntrinsicBall.CM.sourceNativeBallPoint K B z =
      SourceIntrinsicBall.CM.sourceNativeBallPoint K B (BallLineAction.CM.ballPrincipalAction K B g hg.1 z) :=
  SourceIntrinsicLine.CM.source_native_principal_ball_action K Q hμ B.other_place N g hg z

theorem direct_single_native_half_factor (z : B.Domain) :
    RepresentationTheory.Theta.Adelic.BallNatural.Factors.naturalHalfFactor 1
      (RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) (singleSourceArchimedeanElement K Q N g hg))
      (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) =
      (BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2 := by
  exact (pow_one _).trans (SourceIntrinsicLine.CM.direct_source_native_denominator K Q hμ B.other_place N g hg z)

theorem direct_single_native_unnormalized_matrix (τ : Fin places.count) :
    IntrinsicPairedAction.CM.nativeUnnormalizedTensorMatrix (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j)
      (singleSourceArchimedeanElement K Q N g hg) τ =
      SourceSymplecticAction.CM.ballEmbeddingMatrix K g (places.representative τ) ⊗ₖ (1 : Matrix (Fin 1) (Fin 1) ℂ) :=
  congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M ⊗ₖ (1 : Matrix (Fin 1) (Fin 1) ℂ))
    (SourceIntrinsicLine.CM.direct_source_rational_local_matrix K Q N g hg τ)

theorem direct_single_source_paired_action (w : HeckeCycles.GeometricSource.CM.Ambient K) :
    SingleLineComponents.CM.singleSourcePairedCoordinates K places (SourceSymplecticAction.CM.ballAmbientAction K g w) =
      IntrinsicPairedAction.CM.nativePairedActionLinear (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) (singleSourceArchimedeanElement K Q N g hg)
        (SingleLineComponents.CM.singleSourcePairedCoordinates K places w) := by
  refine funext (fun τ : Fin places.count => ?_)
  apply Prod.ext
  · funext ij
    have hm := congrArg (fun M : Matrix (Fin 3 × Fin 1) (Fin 3 × Fin 1) ℂ =>
      M.mulVec (SingleLineComponents.CM.singleSourcePairedCoordinates K places w τ).1 ij)
      (direct_single_native_unnormalized_matrix K Q hμ j N g hg τ)
    have he := RepresentationTheory.Theta.Adelic.TensorGeometricAction.tensor_first_mulVec (SourceSymplecticAction.CM.ballEmbeddingMatrix K g (places.representative τ))
      (SingleLineComponents.CM.singleSourcePairedCoordinates K places w τ).1 ij.1 ij.2
    have hs := congrArg (fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) => p.1 ij.1)
      (SourceFrameAction.CM.ball_ambient_action_paired K places g w τ)
    exact hs.trans (hm.trans he).symm
  · funext ij
    have hm := congrArg (fun M : Matrix (Fin 3 × Fin 1) (Fin 3 × Fin 1) ℂ =>
      (M.map star).mulVec (SingleLineComponents.CM.singleSourcePairedCoordinates K places w τ).2 ij)
      (direct_single_native_unnormalized_matrix K Q hμ j N g hg τ)
    have he := ConcreteApproximationGroupAction.CM.tensor_first_star_mulVec (SourceSymplecticAction.CM.ballEmbeddingMatrix K g (places.representative τ))
      (SingleLineComponents.CM.singleSourcePairedCoordinates K places w τ).2 ij.1 ij.2
    have hc := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ =>
      M.mulVec (fun k => (SingleLineComponents.CM.singleSourcePairedCoordinates K places w τ).2 (k, ij.2)) ij.1)
      (ConcreteApproximationGroupAction.CM.ball_embedding_matrix_conjugate K g (places.representative τ))
    have hs := congrArg (fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) => p.2 ij.1)
      (SourceFrameAction.CM.ball_ambient_action_paired K places g w τ)
    exact hs.trans (hc.trans (hm.trans he).symm)

theorem direct_single_complex_components_action (w : HeckeCycles.GeometricSource.CM.Ambient K) :
    SingleLineComponents.CM.directSingleLineComplexComponents K Q hμ j (SourceSymplecticAction.CM.ballAmbientAction K g w) =
      RepresentationTheory.Theta.Adelic.BallGeometryData.geometricAction (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) (singleSourceArchimedeanElement K Q N g hg)
        (SingleLineComponents.CM.directSingleLineComplexComponents K Q hμ j w) :=
  (congrArg (IntrinsicTensorComplexCoordinates.CM.nativePairedTensorComponents (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j))
    (direct_single_source_paired_action K Q hμ j N g hg w)).trans
      (IntrinsicPairedAction.CM.native_paired_components_action (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j)
        (singleSourceArchimedeanElement K Q N g hg) (SingleLineComponents.CM.singleSourcePairedCoordinates K places w))

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineGroupAction.CM
