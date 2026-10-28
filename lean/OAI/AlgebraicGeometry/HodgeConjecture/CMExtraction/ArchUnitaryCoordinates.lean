import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalPhaseColumn
import OAI.RepresentationTheory.Hecke.RadialDilation.RationalCoordinates

/-! # Arch Unitary Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ArchUnitaryCoordinates.Intrinsic

noncomputable section

/-! The actual rational SU action in paired archimedean coordinates,
using the same rational basis as the signed native period. -/

open OAI.RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization
open scoped Classical TensorProduct _root_.Matrix

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

def pairedUnitaryEnd (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) :
    Module.End ℂ (Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) :=
  LinearMap.pi fun τ =>
    ((g.val.val.map (P.embeddings τ)).mulVecLin.prodMap
      (g.val.val.map (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings τ))).mulVecLin).comp (LinearMap.proj τ)

theorem embeddingCoordinates_unitary (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (x : Fin 3 → E) :
    Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings (RationalPhaseColumn.Intrinsic.rationalUnitaryEnd E P g x) =
      pairedUnitaryEnd E P g (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings x) := by
  funext τ
  apply Prod.ext
  · funext i
    exact RingHom.map_mulVec (P.embeddings τ).toRingHom g.val.val x i
  · funext i
    exact RingHom.map_mulVec (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings τ)).toRingHom g.val.val x i

theorem pairedComplexification_unitary (hσ : Function.Bijective (RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.pairingEmbeddings P.embeddings))
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (x : ComplexMultiplication.WeightOne.CM.Complexification (Fin 3 → E)) :
    RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.pairedComplexification E P.embeddings hσ ((RationalPhaseColumn.Intrinsic.rationalUnitaryEnd E P g).baseChange ℂ x) =
      pairedUnitaryEnd E P g (RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.pairedComplexification E P.embeddings hσ x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul z x =>
      rw [LinearMap.baseChange_tmul, RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.pairedComplexification_tmul,
        RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.pairedComplexification_tmul, map_smul, embeddingCoordinates_unitary]

theorem rational_matrix_realizes_unitary (hσ : Function.Bijective (RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.pairingEmbeddings P.embeddings))
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) :
    RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates E P.embeddings hσ e (pairedUnitaryEnd E P g u) =
      (RationalPhaseColumn.Intrinsic.rationalUnitaryMatrix E P e g).map (algebraMap ℚ ℂ) *ᵥ
        RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates E P.embeddings hσ e u := by
  obtain ⟨x, rfl⟩ := (RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.pairedComplexification E P.embeddings hσ).surjective u
  rw [← pairedComplexification_unitary E P hσ]
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, Matrix.mulVec_add]
  | tmul z x =>
      rw [LinearMap.baseChange_tmul, RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates_tmul, RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates_tmul,
        Matrix.mulVec_smul, RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rational_matrix_complex_mulVec, RationalPhaseColumn.Intrinsic.rationalUnitaryMatrix_apply]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ArchUnitaryCoordinates.Intrinsic
