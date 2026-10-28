import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceSymplecticAction
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallLineAction

/-! # Ball Ambient Pairing -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallAmbientPairing.CM

noncomputable section

/-! ThetaCycle: the actual Galois-component action preserves the bilinear
pairing between conjugate components and the negative line chart. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsGalois ℚ K]
  [NumberField.IsCMField K]

omit [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K] in
theorem local_pairing_matrix (b : K) (τ : Gal(K/ℚ)) (x y : HeckeCycles.GeometricSource.CM.Vec ℂ) :
    (Matrix.diagonal (fun i : Fin 3 => if i = 2 then (τ b : ℂ) else 1)).toBilin' x y =
      HeckeCycles.GeometricSource.CM.localPairing K b τ x y := by
  simp only [Matrix.toBilin'_apply', Matrix.mulVec_diagonal, dotProduct, HeckeCycles.GeometricSource.CM.localPairing]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem ball_embedding_pairing_matrix (B : HeckeCycles.GeometricSource.CM.BallDatum K) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
    (hg : ∀ x y, HeckeCycles.GeometricSource.CM.hermitian K B.b (g x) (g y) = HeckeCycles.GeometricSource.CM.hermitian K B.b x y)
    (τ : Gal(K/ℚ)) :
    (SourceSymplecticAction.CM.ballEmbeddingMatrix K g τ).transpose *
      Matrix.diagonal (fun i : Fin 3 => if i = 2 then (τ B.b : ℂ) else 1) *
        SourceSymplecticAction.CM.ballEmbeddingMatrix K g (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * τ) =
      Matrix.diagonal (fun i : Fin 3 => if i = 2 then (τ B.b : ℂ) else 1) := by
  have hc (x : K) : ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K τ (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K x) =
      ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * τ) x := by
    change (τ (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K x) : ℂ) = ((ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * τ) x : ℂ)
    exact congrArg (fun σ : Gal(K/ℚ) => (σ x : ℂ)) (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_commute K τ).eq.symm
  apply Matrix.ext
  intro i j
  have hs : HeckeCycles.GeometricSource.CM.hermitian K B.b (Pi.single i 1) (Pi.single j 1) =
      if i = j then (if i = 2 then B.b else 1) else 0 := by
    by_cases hij : i = j
    · subst j
      simp [HeckeCycles.GeometricSource.CM.hermitian, Pi.single_apply, eq_comm]
    · simp [HeckeCycles.GeometricSource.CM.hermitian, Pi.single_apply, eq_comm, hij]
  have he := congrArg (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K τ) (hg (Pi.single i 1) (Pi.single j 1))
  rw [hs] at he
  simp only [HeckeCycles.GeometricSource.CM.hermitian, map_sum, map_mul, hc, apply_ite (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K τ),
    map_one, map_zero, ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv_apply] at he
  change (∑ k, ((SourceSymplecticAction.CM.ballEmbeddingMatrix K g τ).transpose *
    Matrix.diagonal (fun a : Fin 3 => if a = 2 then (τ B.b : ℂ) else 1)) i k *
      SourceSymplecticAction.CM.ballEmbeddingMatrix K g (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * τ) k j) = _
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, SourceSymplecticAction.CM.ballEmbeddingMatrix,
    Matrix.map_apply, Matrix.diagonal_apply, LinearMap.toMatrix'_apply,
    LinearEquiv.coe_coe, ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv_apply]
  convert he using 1
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem ball_embedding_local_pairing (B : HeckeCycles.GeometricSource.CM.BallDatum K) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
    (hg : ∀ x y, HeckeCycles.GeometricSource.CM.hermitian K B.b (g x) (g y) = HeckeCycles.GeometricSource.CM.hermitian K B.b x y)
    (τ : Gal(K/ℚ)) (x y : HeckeCycles.GeometricSource.CM.Vec ℂ) :
    HeckeCycles.GeometricSource.CM.localPairing K B.b τ ((SourceSymplecticAction.CM.ballEmbeddingMatrix K g τ).mulVec x)
        ((SourceSymplecticAction.CM.ballEmbeddingMatrix K g (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * τ)).mulVec y) =
      HeckeCycles.GeometricSource.CM.localPairing K B.b τ x y := by
  have he := Matrix.toBilin'_comp
    (Matrix.diagonal (fun i : Fin 3 => if i = 2 then (τ B.b : ℂ) else 1))
    (SourceSymplecticAction.CM.ballEmbeddingMatrix K g τ) (SourceSymplecticAction.CM.ballEmbeddingMatrix K g (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * τ))
  rw [ball_embedding_pairing_matrix K B g hg τ] at he
  have hv := congrArg (fun q : LinearMap.BilinForm ℂ (HeckeCycles.GeometricSource.CM.Vec ℂ) => q x y) he
  simpa only [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply, local_pairing_matrix] using hv

omit [NumberField K] [NumberField.IsCMField K] in
theorem ball_embedding_matrix_identity (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) :
    SourceSymplecticAction.CM.ballEmbeddingMatrix K g 1 = BallActionMatrix.CM.ballActionMatrix K g := rfl

omit [IsGalois ℚ K] in
theorem ball_action_line_vector (B : HeckeCycles.GeometricSource.CM.BallDatum K) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
    (hg : ∀ x y, HeckeCycles.GeometricSource.CM.hermitian K B.b (g x) (g y) = HeckeCycles.GeometricSource.CM.hermitian K B.b x y)
    (z : B.Domain) :
    (BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) =
      ((BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2) •
        HeckeCycles.GeometricSource.CM.BallDatum.lineVector (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val) := by
  have hn := BallLineAction.CM.ball_action_denominator_ne_zero K B g hg z
  let y := (BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val)
  funext i
  fin_cases i
  · change y 0 = y 2 * (y 0 / y 2)
    exact (mul_div_cancel₀ _ hn).symm
  · change y 1 = y 2 * (y 1 / y 2)
    exact (mul_div_cancel₀ _ hn).symm
  · change y 2 = y 2 * 1
    exact (mul_one _).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallAmbientPairing.CM
