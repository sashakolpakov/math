import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RankThreeEmbeddingCoordinates

/-! # Complex Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The exact paired embedding coordinates identify the complexified
original E-cube with the ambient space of the reference period family. -/

open scoped TensorProduct

def Reference.ComplexCoordinates.pairedEmbeddingCoordinates (s : ℕ) :
    ((Fin s × Bool) → Fin 3 → ℂ) ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) where
  toFun f i := (f (i, false), f (i, true))
  invFun f p := if p.2 then (f p.1).2 else (f p.1).1
  left_inv f := by
    funext p
    rcases p with ⟨i, b⟩
    cases b <;> rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} (P : Datum.RankThreePELDatum E s)

def Datum.RankThreePELDatum.embeddingEnumeration (hP : P.IsAdmissible) : (Fin s × Bool) ≃ (E →ₐ[ℚ] ℂ) :=
  Equiv.ofBijective (fun p => if p.2 then ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings p.1)
    else P.embeddings p.1) hP.1

def Datum.RankThreePELDatum.referenceComplexCoordinates (hP : P.IsAdmissible) :
    ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) :=
  (RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates E).trans
    ((LinearEquiv.piCongrLeft ℂ (fun _ : Fin s × Bool => Fin 3 → ℂ)
      (P.embeddingEnumeration hP).symm).trans (Reference.ComplexCoordinates.pairedEmbeddingCoordinates s))

theorem Datum.RankThreePELDatum.referenceComplexCoordinates_tmul (hP : P.IsAdmissible) (c : ℂ) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    P.referenceComplexCoordinates hP (c ⊗ₜ[ℚ] v) = c • Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings v := by
  funext i
  apply Prod.ext
  · funext j
    simpa [Datum.RankThreePELDatum.referenceComplexCoordinates, Reference.ComplexCoordinates.pairedEmbeddingCoordinates, Datum.RankThreePELDatum.embeddingEnumeration,
      LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft', Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates]
      using RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates_tmul E c v (P.embeddings i) j
  · funext j
    simpa [Datum.RankThreePELDatum.referenceComplexCoordinates, Reference.ComplexCoordinates.pairedEmbeddingCoordinates, Datum.RankThreePELDatum.embeddingEnumeration,
      LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft', Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates]
      using RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates_tmul E c v (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)) j

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
