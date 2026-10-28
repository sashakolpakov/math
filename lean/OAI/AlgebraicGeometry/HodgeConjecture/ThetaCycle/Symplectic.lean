import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Lagrangians
import OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticBasis

/-! # Symplectic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Symplectic.CM

noncomputable section

/-! Construct rational symplectic coordinates for the actual trace form and
identify their complex extension with HeckeCycles's Galois-indexed ambient space. -/

open scoped Classical TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]

def galoisToPaired (places : HeckeCycles.GeometricSource.CM.Places K) : HeckeCycles.GeometricSource.CM.Ambient K ≃ₗ[ℂ] Lagrangians.CM.pairedAmbient K places :=
  (LinearEquiv.funCongrLeft ℂ (HeckeCycles.GeometricSource.CM.Vec ℂ) (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K).symm).trans
    (RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.pairedFunctionEquiv (HeckeCycles.ReferenceDatum.CM.embeddings K places) (HeckeCycles.ReferenceDatum.CM.embeddings_complete K places))

theorem galoisToPaired_apply (places : HeckeCycles.GeometricSource.CM.Places K) (w : HeckeCycles.GeometricSource.CM.Ambient K)
    (i : Fin places.count) :
    galoisToPaired K places w i =
      (w (places.representative i), w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * places.representative i)) := by
  change (w ((ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K).symm (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K (places.representative i))),
    w ((ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K).symm (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K (places.representative i))))) = _
  rw [← ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv_conjugation, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem galoisToPaired_embedding (places : HeckeCycles.GeometricSource.CM.Places K) (x : HeckeCycles.GeometricSource.CM.Vec K) :
    galoisToPaired K places (HeckeCycles.GeometricSource.CM.embeddingCoordinates K x) =
      Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates (HeckeCycles.ReferenceDatum.CM.embeddings K places) x := by
  funext i
  rw [galoisToPaired_apply]
  apply Prod.ext
  · rfl
  · funext j
    exact congrArg (fun σ : K →ₐ[ℚ] ℂ => σ (x j))
      (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv_conjugation K (places.representative i))

theorem rational_coordinates_embedding (places : HeckeCycles.GeometricSource.CM.Places K)
    (e : (HeckeCycles.GeometricSource.CM.Vec K) ≃ₗ[ℚ] (Sum (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places) → ℚ))
    (x : HeckeCycles.GeometricSource.CM.Vec K) :
    RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates K (HeckeCycles.ReferenceDatum.CM.embeddings K places) (HeckeCycles.ReferenceDatum.CM.embeddings_complete K places) e
      (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates (HeckeCycles.ReferenceDatum.CM.embeddings K places) x) =
        fun i => (e x i : ℂ) := by
  have h := RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates_tmul K (HeckeCycles.ReferenceDatum.CM.embeddings K places) (HeckeCycles.ReferenceDatum.CM.embeddings_complete K places) e 1 x
  rw [RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.pairedComplexification_tmul K (HeckeCycles.ReferenceDatum.CM.embeddings K places) (HeckeCycles.ReferenceDatum.CM.embeddings_complete K places) 1 x,
    one_smul, one_smul] at h
  exact h

theorem exists_symplectic_coordinates (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (a δ : K) (ha : a ≠ 0) (hac : ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K a = a)
    (hδ : δ ≠ 0) (hδc : ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K δ = -δ) :
    ∃ C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places, C.a = a ∧ C.delta = δ := by
  have hb : B.b ≠ 0 := by
    intro h
    have hn := B.negative
    simp only [h, IntermediateField.coe_zero, Complex.zero_re, lt_self_iff_false] at hn
  have hdet : (Matrix.diagonal ![1, 1, B.b]).det ≠ 0 := by
    simpa [Matrix.det_diagonal, Fin.prod_univ_succ] using hb
  obtain ⟨e, he⟩ := RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization.exists_rational_symplectic_coordinates K
    (HeckeCycles.ReferenceDatum.CM.embeddings K places) (HeckeCycles.ReferenceDatum.CM.embeddings_complete K places) δ a hδc hac (mul_ne_zero hδ ha)
    (Matrix.diagonal ![1, 1, B.b]) (NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.diagonal_hermitian B.b B.conjugate_b) hdet
  let rq := e.trans (LinearEquiv.sumArrowLequivProdArrow (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places) ℚ ℚ)
  let cc := (galoisToPaired K places).trans
    ((RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates K (HeckeCycles.ReferenceDatum.CM.embeddings K places) (HeckeCycles.ReferenceDatum.CM.embeddings_complete K places) e).trans
      (LinearEquiv.sumArrowLequivProdArrow (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places) ℂ ℂ))
  have hext : ∀ x, cc (HeckeCycles.GeometricSource.CM.embeddingCoordinates K x) =
      (fun j => ((rq x).1 j : ℂ), fun j => ((rq x).2 j : ℂ)) := by
    intro x
    change (LinearEquiv.sumArrowLequivProdArrow _ _ ℂ ℂ)
      (RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates K (HeckeCycles.ReferenceDatum.CM.embeddings K places) (HeckeCycles.ReferenceDatum.CM.embeddings_complete K places) e
        (galoisToPaired K places (HeckeCycles.GeometricSource.CM.embeddingCoordinates K x))) = _
    rw [galoisToPaired_embedding, rational_coordinates_embedding]
    rfl
  have hpair : ∀ x y, Algebra.trace ℚ K (δ * a * HeckeCycles.GeometricSource.CM.hermitian K B.b x y) =
      ∑ j, ((rq x).1 j * (rq y).2 j - (rq y).1 j * (rq x).2 j) := by
    intro x y
    have hp := he x y
    rw [RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization.rationalTraceForm_apply, NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.trace_matrix_diagonal] at hp
    change Algebra.trace ℚ K (δ * a * NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian B.b x y) = _
    rw [← hp]
    apply Finset.sum_congr rfl
    intro j _
    change e x (Sum.inl j) * e y (Sum.inr j) - e x (Sum.inr j) * e y (Sum.inl j) =
      e x (Sum.inl j) * e y (Sum.inr j) - e y (Sum.inl j) * e x (Sum.inr j)
    ring
  exact ⟨⟨a, ha, hac, δ, hδ, hδc, rq, cc, hext, hpair⟩, rfl, rfl⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Symplectic.CM
