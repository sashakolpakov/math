import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallAmbientPairing

/-! # Ball Prescribed Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallPrescribedAction.CM

noncomputable section

/-! ThetaCycle: the literal principal ball action carries each source
prescribed Hodge subspace to the prescribed subspace at the image point. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]

omit [NumberField K] [NumberField.IsCMField K] in
theorem local_pairing_smul_left (b : K) (τ : Gal(K/ℚ)) (c : ℂ) (x y : HeckeCycles.GeometricSource.CM.Vec ℂ) :
    HeckeCycles.GeometricSource.CM.localPairing K b τ (c • x) y = c * HeckeCycles.GeometricSource.CM.localPairing K b τ x y := by
  simp only [HeckeCycles.GeometricSource.CM.localPairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

variable [IsGalois ℚ K]

theorem ball_action_prescribed (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Gal(K/ℚ) → Bool) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
    (hg : ∀ x y, HeckeCycles.GeometricSource.CM.hermitian K B.b (g x) (g y) = HeckeCycles.GeometricSource.CM.hermitian K B.b x y)
    (z : B.Domain) (w : HeckeCycles.GeometricSource.CM.Ambient K) (hw : HeckeCycles.GeometricSource.CM.prescribed K B places d z.val w) :
    HeckeCycles.GeometricSource.CM.prescribed K B places d (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val) (SourceSymplecticAction.CM.ballAmbientAction K g w) := by
  intro i
  by_cases hi : i = places.distinguished
  · subst i
    have hwi := hw places.distinguished
    simp only [places.identity, mul_one] at hwi ⊢
    let den := (BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2
    constructor
    · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hwi.1
      apply Submodule.mem_span_singleton.mpr
      refine ⟨c * den, ?_⟩
      change (c * den) • HeckeCycles.GeometricSource.CM.BallDatum.lineVector (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val) =
        (SourceSymplecticAction.CM.ballEmbeddingMatrix K g 1).mulVec (w 1)
      rw [← hc, Matrix.mulVec_smul, BallAmbientPairing.CM.ball_embedding_matrix_identity,
        BallAmbientPairing.CM.ball_action_line_vector K B g hg z, mul_smul]
    · have he := BallAmbientPairing.CM.ball_embedding_local_pairing K B g hg 1
        (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) (w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K))
      rw [BallAmbientPairing.CM.ball_embedding_matrix_identity, BallAmbientPairing.CM.ball_action_line_vector K B g hg z,
        local_pairing_smul_left, hwi.2] at he
      have hz := (mul_eq_zero.mp he).resolve_left (BallLineAction.CM.ball_action_denominator_ne_zero K B g hg z)
      simpa only [mul_one] using! hz
  · have hwi := hw i
    simp only [ite_eq_right hi] at hwi ⊢
    split_ifs with hd
    · rw [ite_eq_left hd] at hwi
      change (SourceSymplecticAction.CM.ballEmbeddingMatrix K g (places.representative i)).mulVec (w (places.representative i)) = 0
      rw [hwi, Matrix.mulVec_zero]
    · rw [ite_eq_right hd] at hwi
      change (SourceSymplecticAction.CM.ballEmbeddingMatrix K g (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * places.representative i)).mulVec
        (w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * places.representative i)) = 0
      rw [hwi, Matrix.mulVec_zero]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallPrescribedAction.CM
