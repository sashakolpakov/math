import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineFrameAction
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineLevel
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleSourceCotangentAction
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceBallCovariance

/-! # Single Line Descent -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineDescent.CM

noncomputable section

section

/-! The same-input native law gives literal covariance of the full
source tensor and invariance of the actual source one-form. -/

open scoped Classical _root_.NumberField _root_.Matrix _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]

def singleSourceAdaptedThetaTensor {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}
    {d : Gal(K/ℚ) → Bool} (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places)) (a : ℕ) (z : HeckeCycles.GeometricSource.CM.BallChart) :
    ContinuousMultilinearMap ℂ (fun _ : Fin a => HeckeCycles.GeometricSource.CM.Positions K places → ℂ) ℂ :=
  (L.halfDet z : ℂ) •
    (iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ (L.period z)) 0).compContinuousLinearMap
      (fun _ => (Matrix.toLin' (SourceHalfDetAction.CM.sourceAdaptedGraphMatrix K L z)ᵀ).toContinuousLinearMap)

variable {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun k v => d k (places.representative v)))
  (hμ : ∀ k, d k (places.representative places.distinguished) = true) (j : Fin 2)
  (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j)) (hL : L.coordinates.a = Q.a j ∧ L.coordinates.delta = Q.delta)
  (N : ℕ) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel N g)

omit N g hg in
theorem direct_single_native_source_adapted_tensor (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places))
    (z₀ z : B.Domain) (a : ℕ) (u : Fin a → HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor (SingleLineComponents.CM.directSingleLineComparison K Q hμ j)
      (SingleLineComparison.CM.directSingleNativeFiniteInput K Q hμ j L.coordinates hL φ) a
      (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) (fun k => SingleLineGeometricTensor.CM.directSingleNativeDualCoordinates K d Q j (u k)) =
      (((Nat.factorial a : ℂ)⁻¹) * SingleLineHalfRatio.CM.singleSourceNativeHalfRatio K d Q hμ j L hL z₀) *
        singleSourceAdaptedThetaTensor K L φ a z.val u := by
  have h := SingleLineGeometricTensor.CM.single_source_native_geometric_tensor K d Q hμ j L hL φ z₀ z a u
  simpa only [singleSourceAdaptedThetaTensor, _root_.smul_apply, smul_eq_mul,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, mul_assoc] using! h

theorem direct_single_source_tensor_covariant (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places))
    (hcov : SingleLineLevel.CM.SingleSourceThetaCovariant K d Q hμ j L hL φ N g hg)
    (z : B.Domain) (a : ℕ) (u : Fin a → HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    singleSourceAdaptedThetaTensor K L φ a (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val)
      (fun k => (SourceFrameAction.CM.sourceFrameMatrix K g hg.2.1 B places (d j) z.val)⁻¹ᵀ.mulVec (u k)) =
      ((BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2) *
        singleSourceAdaptedThetaTensor K L φ a z.val u := by
  let z' := BallLineAction.CM.ballPrincipalAction K B g hg.1 z
  let S := SourceFrameAction.CM.sourceFrameMatrix K g hg.2.1 B places (d j) z.val
  let c := ((Nat.factorial a : ℂ)⁻¹) * SingleLineHalfRatio.CM.singleSourceNativeHalfRatio K d Q hμ j L hL z
  have hc : c ≠ 0 := mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)))
    (SingleLineHalfRatio.CM.single_source_native_half_ratio_ne_zero K d Q hμ j L hL z)
  have hu : (fun k => SingleLineGeometricTensor.CM.directSingleNativeDualCoordinates K d Q j (S⁻¹ᵀ.mulVec (u k))) =
      (fun k => RepresentationTheory.Theta.Adelic.BallGeometryData.dualFrameChange (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) (SingleLineGroupAction.CM.singleSourceArchimedeanElement K Q N g hg)
        (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) (SingleLineGeometricTensor.CM.directSingleNativeDualCoordinates K d Q j (u k))) :=
    funext (fun k => SingleLineFrameAction.CM.direct_single_dual_frame_action K d Q hμ j N g hg z (u k))
  have hl := direct_single_native_source_adapted_tensor K d Q hμ j L hL φ z z' a (fun k => S⁻¹ᵀ.mulVec (u k))
  have hr := direct_single_native_source_adapted_tensor K d Q hμ j L hL φ z z a u
  have he := congrArg (RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor (SingleLineComponents.CM.directSingleLineComparison K Q hμ j)
    (SingleLineComparison.CM.directSingleNativeFiniteInput K Q hμ j L.coordinates hL φ) a (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z')) hu
  have hn := hcov z a (fun k => SingleLineGeometricTensor.CM.directSingleNativeDualCoordinates K d Q j (u k))
  have ht := congrArg (fun x : ℂ => ((BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2) * x) hr
  apply mul_left_cancel₀ hc
  exact (hl.symm.trans (he.trans (hn.trans ht))).trans (mul_left_comm _ _ _)

theorem direct_single_source_tangent_tensor_covariant (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places))
    (hcov : SingleLineLevel.CM.SingleSourceThetaCovariant K d Q hμ j L hL φ N g hg) (z : B.Domain) (ξ : HeckeCycles.GeometricSource.CM.BallChart) :
    singleSourceAdaptedThetaTensor K L φ 1 (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val)
      (fun _ => SingleSourceCotangentAction.CM.singleAdaptedTangentSlot K places (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val ξ)) =
      singleSourceAdaptedThetaTensor K L φ 1 z.val (fun _ => SingleSourceCotangentAction.CM.singleAdaptedTangentSlot K places ξ) := by
  let S := SourceFrameAction.CM.sourceFrameMatrix K g hg.2.1 B places (d j) z.val
  let κ := (BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2
  let u : Fin 1 → HeckeCycles.GeometricSource.CM.Positions K places → ℂ := fun _ => SingleSourceCotangentAction.CM.singleAdaptedTangentSlot K places ξ
  let u' : Fin 1 → HeckeCycles.GeometricSource.CM.Positions K places → ℂ :=
    fun _ => SingleSourceCotangentAction.CM.singleAdaptedTangentSlot K places (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val ξ)
  let T := singleSourceAdaptedThetaTensor K L φ 1 (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val)
  have hu : (fun i : Fin 1 => S⁻¹ᵀ.mulVec (u i)) = fun i => κ • u' i :=
    funext (fun _ => SingleSourceCotangentAction.CM.single_source_dual_tangent K g hg.2.1 B places (d j) hg.1 z ξ)
  have hs : T (fun i => κ • u' i) = κ * T u' := by
    have h := T.toMultilinearMap.map_smul_univ (fun _ : Fin 1 => κ) u'
    simpa only [Fin.prod_univ_one, smul_eq_mul] using! h
  have ht := congrArg T hu
  have hn := direct_single_source_tensor_covariant K d Q hμ j L hL N g hg φ hcov z 1 u
  exact mul_left_cancel₀ (BallLineAction.CM.ball_action_denominator_ne_zero K B g hg.1 z) (hs.symm.trans (ht.symm.trans hn))

end

/-! Every fixed original one-line theta input descends at all multiples
of one actual principal level. The representative is the literal pure
closed source form, so it supplies the full HeckeCycles source predicate. -/

open scoped Classical _root_.NumberField _root_.Matrix _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}

section SourceProjection
variable {d : Gal(K/ℚ) → Bool} (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)

omit [IsGalois ℚ K] in
theorem single_source_adapted_tensor_slot (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places)) (z : HeckeCycles.GeometricSource.CM.BallChart) (i : Fin 2) :
    singleSourceAdaptedThetaTensor K L φ 1 z (fun _ => SingleAdaptedDualSlots.CM.singleAdaptedDualSlot K places i) =
      Slots.CM.sourceThetaCoordinates K L φ z i := by
  simp only [singleSourceAdaptedThetaTensor, _root_.smul_apply, smul_eq_mul,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_one_apply]
  exact (congrArg ((L.halfDet z : ℂ) * ·)
    (congrArg (fderiv ℂ (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ (L.period z)) 0)
      (SingleAdaptedDualSlots.CM.theta_jacobi_slot_adapted_transpose K L z i).symm)).trans
        (Slots.CM.source_coordinates_completed_slots K L φ z i).symm

omit [IsGalois ℚ K] in
theorem single_source_adapted_tensor_tangent (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places)) (z ξ : HeckeCycles.GeometricSource.CM.BallChart) :
    singleSourceAdaptedThetaTensor K L φ 1 z (fun _ => SingleSourceCotangentAction.CM.singleAdaptedTangentSlot K places ξ) =
      HeckeCycles.GeometricSource.CM.thetaOneForm K L φ z ξ := by
  let l : (HeckeCycles.GeometricSource.CM.Positions K places → ℂ) →L[ℂ] ℂ :=
    (L.halfDet z : ℂ) • (fderiv ℂ (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ (L.period z)) 0).comp
      (Matrix.toLin' (SourceHalfDetAction.CM.sourceAdaptedGraphMatrix K L z)ᵀ).toContinuousLinearMap
  have he (u : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
      singleSourceAdaptedThetaTensor K L φ 1 z (fun _ => u) = l u := by
    simp only [singleSourceAdaptedThetaTensor, _root_.smul_apply, smul_eq_mul,
      ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_one_apply]
    rfl
  have hi (i : Fin 2) : l (SingleAdaptedDualSlots.CM.singleAdaptedDualSlot K places i) = Slots.CM.sourceThetaCoordinates K L φ z i :=
    (he _).symm.trans (single_source_adapted_tensor_slot K L φ z i)
  have hb := congrArg (Projection.CM.sourceThetaCovector K L φ z) ((Pi.basisFun ℂ (Fin 2)).sum_repr ξ)
  simp only [map_sum, map_smul, Pi.basisFun_repr, smul_eq_mul] at hb
  rw [he, SingleSourceCotangentAction.CM.singleAdaptedTangentSlot, map_sum]
  simp only [map_smul, smul_eq_mul, hi]
  have hc (i : Fin 2) : Slots.CM.sourceThetaCoordinates K L φ z i =
      Projection.CM.sourceThetaCovector K L φ z ((Pi.basisFun ℂ (Fin 2)) i) := by
    apply congrArg (Projection.CM.sourceThetaCovector K L φ z)
    funext k
    simp only [Pi.basisFun_apply, Pi.single_apply]
    split_ifs <;> rfl
  exact (Finset.sum_congr rfl (fun i _ => congrArg (ξ i * ·) (hc i))).trans
    (hb.trans (Projection.CM.source_theta_covector_apply K L φ z ξ))

end SourceProjection

variable (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun k v => d k (places.representative v)))
  (hμ : ∀ k, d k (places.representative places.distinguished) = true) (j : Fin 2)
  (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j)) (hL : L.coordinates.a = Q.a j ∧ L.coordinates.delta = Q.delta)

theorem direct_single_source_ball_invariant (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places))
    (N : ℕ) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel N g)
    (hcov : SingleLineLevel.CM.SingleSourceThetaCovariant K d Q hμ j L hL φ N g hg) :
    (BallForms.CM.sourceBallOneForm K L φ).val.pullback (BallLineAction.CM.ballPrincipalAction K B g hg.1) = (BallForms.CM.sourceBallOneForm K L φ).val := by
  apply SourceBallCovariance.CM.source_ball_pullback_of_cotangent K g hg.1 L φ φ
  intro z ξ
  have h := direct_single_source_tangent_tensor_covariant K d Q hμ j L hL N g hg φ hcov z ξ
  simpa only [single_source_adapted_tensor_tangent] using h

include hμ hL

theorem exists_single_source_ball_invariant_level (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places)) :
    ∃ M : ℕ, 0 < M ∧ ∀ N : ℕ, M ∣ N →
      ∀ (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel N g),
        (BallForms.CM.sourceBallOneForm K L φ).val.pullback (BallLineAction.CM.ballPrincipalAction K B g hg.1) =
          (BallForms.CM.sourceBallOneForm K L φ).val := by
  have h := SingleLineLevel.CM.exists_single_source_theta_level K d Q hμ j L hL φ
  refine ⟨h.choose, h.choose_spec.1, ?_⟩
  intro N hN g hg
  exact direct_single_source_ball_invariant K d Q hμ j L hL φ N g hg (h.choose_spec.2 N hN g hg)

theorem exists_single_source_descent_level (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places)) :
    ∃ M : ℕ, 0 < M ∧ ∀ N : ℕ, M ∣ N →
      ∀ (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : B.Domain → X.analyticSpace) (hπ : B.IsBallCover N X π),
        ∃ a : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0,
          CoverPullback.CM.ballCoverPullback K B N X π hπ 1 a.val.val = BallForms.CM.sourceBallOneForm K L φ ∧
          HeckeCycles.GeometricSource.CM.RepresentsTheta K L φ X π a := by
  have h := exists_single_source_ball_invariant_level K d Q hμ j L hL φ
  refine ⟨h.choose, h.choose_spec.1, ?_⟩
  intro N hN X π hπ
  exact SourceDescent.CM.exists_source_theta_descent K L φ N X π hπ (h.choose_spec.2 N hN)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineDescent.CM
