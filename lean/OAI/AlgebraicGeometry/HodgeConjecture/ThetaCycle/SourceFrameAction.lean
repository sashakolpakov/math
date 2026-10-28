import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallFrameMatrices
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoefficientPeriods

/-! # Source Frame Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceFrameAction.CM

noncomputable section

/-! ThetaCycle: the actual source line-annihilator frame transforms by an
explicit block matrix over all places. Its determinant is the square of
the projective denominator; every compact block has determinant one. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsGalois ℚ K]
  [NumberField.IsCMField K]

theorem source_local_frame_weighted (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (i : Fin places.count) (z : HeckeCycles.GeometricSource.CM.BallChart) (u : Fin 3 → ℂ) :
    Geometry.ComplexBall.PrescribedSignsB.localFrame (CoefficientPeriods.CM.ballMatrix K B places i) z u =
      CMExtraction.UnitaryFrameAction.weightedFrame (HeckeCycles.ReferenceDatum.CM.embeddings K places i B.b) z u := by
  have hB : CoefficientPeriods.CM.ballMatrix K B places i =
      Matrix.toBilin' (CMExtraction.UnitaryFrameAction.diagonalForm (HeckeCycles.ReferenceDatum.CM.embeddings K places i B.b)) := by
    apply congrArg Matrix.toBilin'
    apply Matrix.ext
    intro j k
    fin_cases j <;> fin_cases k <;> simp [CMExtraction.UnitaryFrameAction.diagonalForm]
  rw [hB]
  ext j <;> fin_cases j <;>
    simp [Geometry.ComplexBall.PrescribedSignsB.localFrame, Geometry.ComplexBall.PrescribedSignsB.axis, Geometry.ComplexBall.PrescribedSignsB.lineVector,
      Matrix.toBilin'_apply, CMExtraction.UnitaryFrameAction.diagonalForm, CMExtraction.UnitaryFrameAction.weightedFrame, CMExtraction.UnitaryFrameAction.weightedAnnihilator,
      RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector, Fin.sum_univ_succ]
  ring

theorem ball_ambient_action_paired (places : HeckeCycles.GeometricSource.CM.Places K) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
    (w : HeckeCycles.GeometricSource.CM.Ambient K) (i : Fin places.count) :
    Symplectic.CM.galoisToPaired K places (SourceSymplecticAction.CM.ballAmbientAction K g w) i =
      ((SourceSymplecticAction.CM.ballEmbeddingMatrix K g (places.representative i)).mulVec (Symplectic.CM.galoisToPaired K places w i).1,
        (SourceSymplecticAction.CM.ballEmbeddingMatrix K g (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * places.representative i)).mulVec
          (Symplectic.CM.galoisToPaired K places w i).2) := by
  rw [Symplectic.CM.galoisToPaired_apply, Symplectic.CM.galoisToPaired_apply]
  rfl

variable (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hdet : LinearMap.det g.toLinearMap = 1)
  (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K) (d : Gal(K/ℚ) → Bool)

def sourceFramePlaceMatrix (z : HeckeCycles.GeometricSource.CM.BallChart) (i : Fin places.count) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  if i = places.distinguished then BallFrameMatrices.CM.sourceActiveFrameMatrix K g hdet B z
  else if d (places.representative i) then SourceSymplecticAction.CM.ballEmbeddingMatrix K g (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * places.representative i)
  else SourceSymplecticAction.CM.ballEmbeddingMatrix K g (places.representative i)

def sourceFrameMatrix (z : HeckeCycles.GeometricSource.CM.BallChart) : Matrix (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places) ℂ :=
  Matrix.reindexRingEquiv ℂ (Equiv.prodComm (Fin 3) (Fin places.count))
    (Matrix.blockDiagonal (sourceFramePlaceMatrix K g hdet B places d z))

theorem source_frame_matrix_entry (z : HeckeCycles.GeometricSource.CM.BallChart) (i j : Fin places.count) (a b : Fin 3) :
    sourceFrameMatrix K g hdet B places d z (i, a) (j, b) =
      if i = j then sourceFramePlaceMatrix K g hdet B places d z i a b else 0 := rfl

theorem source_frame_matrix_mulVec (z : HeckeCycles.GeometricSource.CM.BallChart) (x : HeckeCycles.GeometricSource.CM.Positions K places → ℂ)
    (i : Fin places.count) (a : Fin 3) :
    (sourceFrameMatrix K g hdet B places d z *ᵥ x) (i, a) =
      (sourceFramePlaceMatrix K g hdet B places d z i *ᵥ (fun b => x (i, b))) a := by
  change (∑ j, sourceFrameMatrix K g hdet B places d z (i, a) j * x j) = _
  simp [Fintype.sum_prod_type, source_frame_matrix_entry, Matrix.mulVec, dotProduct]

theorem source_frame_place_compact_det (z : HeckeCycles.GeometricSource.CM.BallChart) (i : Fin places.count)
    (hi : i ≠ places.distinguished) :
    (sourceFramePlaceMatrix K g hdet B places d z i).det = 1 := by
  unfold sourceFramePlaceMatrix
  rw [ite_eq_right hi]
  split_ifs
  · exact (BallFrameMatrices.CM.ballEmbeddingSL K g hdet (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * places.representative i)).property
  · exact (BallFrameMatrices.CM.ballEmbeddingSL K g hdet (places.representative i)).property

variable (hg : ∀ x y, HeckeCycles.GeometricSource.CM.hermitian K B.b (g x) (g y) = HeckeCycles.GeometricSource.CM.hermitian K B.b x y)

include hg in
theorem source_frame_matrix_det (z : HeckeCycles.GeometricSource.CM.BallChart) :
    (sourceFrameMatrix K g hdet B places d z).det =
      ((BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z) 2) ^ 2 := by
  change (Matrix.reindex (Equiv.prodComm (Fin 3) (Fin places.count))
    (Equiv.prodComm (Fin 3) (Fin places.count))
    (Matrix.blockDiagonal (sourceFramePlaceMatrix K g hdet B places d z))).det = _
  rw [Matrix.det_reindex_self, Matrix.det_blockDiagonal,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ places.distinguished)]
  have hp : ∏ i ∈ Finset.univ.erase places.distinguished,
      (sourceFramePlaceMatrix K g hdet B places d z i).det = 1 :=
    Finset.prod_eq_one fun i hi => source_frame_place_compact_det K g hdet B places d z i
      (Finset.mem_erase.mp hi).1
  rw [hp, mul_one]
  change (if places.distinguished = places.distinguished then BallFrameMatrices.CM.sourceActiveFrameMatrix K g hdet B z else _).det = _
  rw [ite_eq_left rfl]
  exact BallFrameMatrices.CM.source_active_frame_matrix_det K g hdet B hg z

include hg in
theorem source_place_frame_transform (z : B.Domain) (i : Fin places.count) (u : Fin 3 → ℂ) :
    ((SourceSymplecticAction.CM.ballEmbeddingMatrix K g (places.representative i)).mulVec
        (Geometry.ComplexBall.PrescribedSignsB.placeFrame (CoefficientPeriods.CM.ballMatrix K B places) places.distinguished
          (fun j => d (places.representative j)) z.val i u).1,
      (SourceSymplecticAction.CM.ballEmbeddingMatrix K g (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * places.representative i)).mulVec
        (Geometry.ComplexBall.PrescribedSignsB.placeFrame (CoefficientPeriods.CM.ballMatrix K B places) places.distinguished
          (fun j => d (places.representative j)) z.val i u).2) =
      Geometry.ComplexBall.PrescribedSignsB.placeFrame (CoefficientPeriods.CM.ballMatrix K B places) places.distinguished
        (fun j => d (places.representative j)) (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val) i
        (sourceFramePlaceMatrix K g hdet B places d z.val i *ᵥ u) := by
  by_cases hi : i = places.distinguished
  · subst i
    simp only [Geometry.ComplexBall.PrescribedSignsB.placeFrame, sourceFramePlaceMatrix, ite_true,
      places.identity, mul_one, source_local_frame_weighted, HeckeCycles.ReferenceDatum.CM.embeddings_distinguished]
    exact BallFrameMatrices.CM.source_weighted_frame_transform K g hdet B hg z u
  · cases hd : d (places.representative i) <;>
      simp [Geometry.ComplexBall.PrescribedSignsB.placeFrame, sourceFramePlaceMatrix, hi, hd]

include hg in
theorem source_native_frame_transform (z : B.Domain) (x : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    SourceSymplecticAction.CM.ballAmbientAction K g (Prescribed.CM.nativePeriodFrame K B places d z.val x) =
      Prescribed.CM.nativePeriodFrame K B places d (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val)
        (sourceFrameMatrix K g hdet B places d z.val *ᵥ x) := by
  apply (Symplectic.CM.galoisToPaired K places).injective
  funext i
  rw [ball_ambient_action_paired]
  simp only [Prescribed.CM.nativePeriodFrame, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  have he : (fun a => (sourceFrameMatrix K g hdet B places d z.val *ᵥ x) (i, a)) =
      sourceFramePlaceMatrix K g hdet B places d z.val i *ᵥ (fun a => x (i, a)) :=
    funext (source_frame_matrix_mulVec K g hdet B places d z.val x i)
  change _ = Geometry.ComplexBall.PrescribedSignsB.placeFrame (CoefficientPeriods.CM.ballMatrix K B places) places.distinguished
    (fun j => d (places.representative j)) (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val) i
      (fun a => (sourceFrameMatrix K g hdet B places d z.val *ᵥ x) (i, a))
  rw [he]
  exact source_place_frame_transform K g hdet B places d hg z i (fun a => x (i, a))

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceFrameAction.CM
