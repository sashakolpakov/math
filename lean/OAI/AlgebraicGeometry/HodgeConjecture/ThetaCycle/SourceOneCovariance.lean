import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceFirstCovariance

/-! # Source One Covariance -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceOneCovariance.CM

noncomputable section

/-! ThetaCycle: the derived geometric theta normalization gives the literal
cotangent pullback equation of the original source one-form. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Gal(K/ℚ) → Bool}

omit [NumberField K] [NumberField.IsCMField K] in
theorem local_pairing_tangent_covector (b : K) (w : HeckeCycles.GeometricSource.CM.Vec ℂ) (ξ : HeckeCycles.GeometricSource.CM.BallChart) :
    HeckeCycles.GeometricSource.CM.localPairing K b 1 ![ξ 0, ξ 1, 0] w =
      CMExtraction.FrameProjection.Multiplicity.coordinateCovector (fun i : Fin 2 => w i.castSucc) ξ := by
  simp [HeckeCycles.GeometricSource.CM.localPairing, CMExtraction.FrameProjection.Multiplicity.coordinateCovector_apply, Fin.sum_univ_succ]
  ring

theorem source_one_coordinate_covector (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places)) (z ξ : HeckeCycles.GeometricSource.CM.BallChart) :
    HeckeCycles.GeometricSource.CM.thetaOneForm K L φ z ξ = (L.halfDet z : ℂ) *
      CMExtraction.FrameProjection.Multiplicity.coordinateCovector (fun i : Fin 2 => Projection.CM.sourceGraphGradient K L φ z (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) i.castSucc) ξ :=
  congrArg ((L.halfDet z : ℂ) * ·) (local_pairing_tangent_covector K B.b _ ξ)

variable [IsGalois ℚ K] (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hdet : LinearMap.det g.toLinearMap = 1)

theorem source_annihilator_action_coordinates (z : HeckeCycles.GeometricSource.CM.BallChart) (w : HeckeCycles.GeometricSource.CM.Vec ℂ)
    (hw : HeckeCycles.GeometricSource.CM.localPairing K B.b 1 (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z) w = 0) :
    (fun i : Fin 2 => (SourceSymplecticAction.CM.ballEmbeddingMatrix K g (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) *ᵥ w) i.castSucc) =
      CMExtraction.UnitaryFrameAction.weightedDualCoordinates (B.b : ℂ) (BallFrameMatrices.CM.ballEmbeddingSL K g hdet (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)) z *ᵥ
        (fun i : Fin 2 => w i.castSucc) := by
  have hb : (B.b : ℂ) ≠ 0 := fun h => (ne_of_lt B.negative) (by rw [h]; rfl)
  have hpair : RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector z ⬝ᵥ
      (CMExtraction.UnitaryFrameAction.diagonalForm (B.b : ℂ)).mulVec w = 0 := by
    simpa [HeckeCycles.GeometricSource.CM.localPairing, HeckeCycles.GeometricSource.CM.BallDatum.lineVector, RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector,
      CMExtraction.UnitaryFrameAction.diagonalForm, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_succ, mul_assoc] using hw
  have hr := CMExtraction.UnitaryFrameAction.weightedAnnihilator_reconstruct (B.b : ℂ) hb z w hpair
  funext i
  conv_lhs => rw [hr]
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change w 0 * ((BallFrameMatrices.CM.ballEmbeddingSL K g hdet (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)).val *ᵥ CMExtraction.UnitaryFrameAction.weightedAnnihilator (B.b : ℂ) z 0) i.castSucc +
    w 1 * ((BallFrameMatrices.CM.ballEmbeddingSL K g hdet (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)).val *ᵥ CMExtraction.UnitaryFrameAction.weightedAnnihilator (B.b : ℂ) z 1) i.castSucc = _
  simp [CMExtraction.UnitaryFrameAction.weightedDualCoordinates, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

variable (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
  (hg : ∀ x y, HeckeCycles.GeometricSource.CM.hermitian K B.b (g x) (g y) = HeckeCycles.GeometricSource.CM.hermitian K B.b x y)

include hg hdet in
theorem source_one_covariance_of_graph_gradient (φ Ψ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places)) (z : B.Domain)
    (h : Projection.CM.sourceGraphGradient K L Ψ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val) =
      SourceHalfDetAction.CM.sourceGeometricMultiplier K L g z.val • SourceSymplecticAction.CM.ballAmbientAction K g (Projection.CM.sourceGraphGradient K L φ z.val))
    (ξ : HeckeCycles.GeometricSource.CM.BallChart) :
    HeckeCycles.GeometricSource.CM.thetaOneForm K L Ψ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val)
        (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val ξ) = HeckeCycles.GeometricSource.CM.thetaOneForm K L φ z.val ξ := by
  let w := Projection.CM.sourceGraphGradient K L φ z.val
  let c : Fin 2 → ℂ := fun i => w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) i.castSucc
  have hp := SourcePeriodAction.CM.source_graph_prescribed K L z
    (fun j => fderiv ℂ (HeckeCycles.GeometricSource.CM.thetaSeries φ (L.period z.val)) 0 (Pi.single j 1)) places.distinguished
  simp only [ite_true, places.identity, mul_one] at hp
  have ha : HeckeCycles.GeometricSource.CM.localPairing K B.b 1 (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) (w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)) = 0 := by
    exact hp.2
  have hv := source_annihilator_action_coordinates K g hdet z.val (w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)) ha
  have hc : (fun i : Fin 2 => Projection.CM.sourceGraphGradient K L Ψ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val)
      (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) i.castSucc) =
        SourceHalfDetAction.CM.sourceGeometricMultiplier K L g z.val •
          (CMExtraction.UnitaryFrameAction.weightedDualCoordinates (B.b : ℂ) (BallFrameMatrices.CM.ballEmbeddingSL K g hdet (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)) z.val *ᵥ c) := by
    rw [h]
    exact congrArg (SourceHalfDetAction.CM.sourceGeometricMultiplier K L g z.val • ·) hv
  rw [source_one_coordinate_covector, source_one_coordinate_covector, hc,
    map_smul CMExtraction.FrameProjection.Multiplicity.coordinateCovector, _root_.smul_apply, smul_eq_mul]
  let v := CMExtraction.FrameProjection.Multiplicity.coordinateCovector
    (CMExtraction.UnitaryFrameAction.weightedDualCoordinates (B.b : ℂ) (BallFrameMatrices.CM.ballEmbeddingSL K g hdet (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)) z.val *ᵥ c)
    (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val ξ)
  change (L.halfDet (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val) : ℂ) *
    (SourceHalfDetAction.CM.sourceGeometricMultiplier K L g z.val * v) = (L.halfDet z.val : ℂ) * CMExtraction.FrameProjection.Multiplicity.coordinateCovector c ξ
  calc
    _ = (L.halfDet z.val : ℂ) *
        (((BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2) * v) := by
      unfold SourceHalfDetAction.CM.sourceGeometricMultiplier
      field_simp
    _ = _ := congrArg ((L.halfDet z.val : ℂ) * ·) (BallProjectiveCotangent.CM.source_ball_projective_cotangent K B g hdet hg z c ξ)

include hg hdet in
theorem exists_source_one_covariant_input (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places)) :
    ∃ Ψ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places), ∀ (z : B.Domain) (ξ : HeckeCycles.GeometricSource.CM.BallChart),
      HeckeCycles.GeometricSource.CM.thetaOneForm K L Ψ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val)
          (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val ξ) = HeckeCycles.GeometricSource.CM.thetaOneForm K L φ z.val ξ := by
  obtain ⟨Ψ, hΨ⟩ := SourceFirstCovariance.CM.exists_source_graph_gradient_covariant_input K L g hg hdet φ
  exact ⟨Ψ, fun z ξ => source_one_covariance_of_graph_gradient K g hdet L hg φ Ψ z (hΨ z) ξ⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceOneCovariance.CM
