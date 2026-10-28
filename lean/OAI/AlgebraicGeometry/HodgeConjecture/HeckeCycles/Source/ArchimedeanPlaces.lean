import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles

/-! # Archimedean Places -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanPlaces.CM

noncomputable section

/-! The original CM representatives enumerate the real places of the
maximal real subfield, with their actual completion coordinates. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.InfinitePlace _root_.NumberField.InfinitePlace.Completion
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [IsCMField E]
  (places : GeometricSource.CM.Places E)

def cmPlace (i : Fin places.count) : InfinitePlace E :=
  InfinitePlace.mk (ReferenceDatum.CM.embeddings E places i).toRingHom

theorem cmPlace_bijective : Function.Bijective (cmPlace E places) := by
  have hc := ReferenceDatum.CM.embeddings_complete E places
  constructor
  · intro i j h
    rcases InfinitePlace.mk_eq_iff.mp h with he | he
    · have he' : ReferenceDatum.CM.embeddings E places i = ReferenceDatum.CM.embeddings E places j := by
        ext x
        exact DFunLike.congr_fun he x
      exact congrArg Prod.fst (hc.1 (a₁ := (i, false)) (a₂ := (j, false)) he')
    · have he' : ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (ReferenceDatum.CM.embeddings E places i) = ReferenceDatum.CM.embeddings E places j := by
        ext x
        exact DFunLike.congr_fun he x
      exact congrArg Prod.fst (hc.1 (a₁ := (i, true)) (a₂ := (j, false)) he')
  · intro w
    obtain ⟨⟨i, b⟩, hi⟩ := hc.2 w.embedding.toRatAlgHom
    refine ⟨i, ?_⟩
    cases b
    · change ReferenceDatum.CM.embeddings E places i = w.embedding.toRatAlgHom at hi
      exact (congrArg InfinitePlace.mk (congrArg AlgHom.toRingHom hi)).trans (mk_embedding w)
    · change ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (ReferenceDatum.CM.embeddings E places i) = w.embedding.toRatAlgHom at hi
      have hm := congrArg InfinitePlace.mk (congrArg AlgHom.toRingHom hi)
      change InfinitePlace.mk (ComplexEmbedding.conjugate (ReferenceDatum.CM.embeddings E places i).toRingHom) =
        InfinitePlace.mk w.embedding at hm
      rw [mk_conjugate_eq, mk_embedding] at hm
      exact hm

def enumeration : Fin places.count ≃ InfinitePlace (QuadraticConjugation.CM.Field.RealField E) :=
  (Equiv.ofBijective (cmPlace E places) (cmPlace_bijective E places)).trans
    (IsCMField.equivInfinitePlace E)

theorem restriction (i : Fin places.count) :
    enumeration E places i = InfinitePlace.mk
      ((ReferenceDatum.CM.embeddings E places i).toRingHom.comp (algebraMap (QuadraticConjugation.CM.Field.RealField E) E)) := rfl

theorem embedding (i : Fin places.count) (x : QuadraticConjugation.CM.Field.RealField E) :
    (embedding_of_isReal (IsTotallyReal.isReal (enumeration E places i)) x : ℂ) =
      ReferenceDatum.CM.embeddings E places i (x : E) := by
  rw [embedding_of_isReal_apply]
  have h := InfinitePlace.embedding_mk_eq_of_isReal
    (IsTotallyReal.complexEmbedding_isReal
      ((ReferenceDatum.CM.embeddings E places i).toRingHom.comp (algebraMap (QuadraticConjugation.CM.Field.RealField E) E)))
  rw [← restriction] at h
  exact congrArg (fun f : QuadraticConjugation.CM.Field.RealField E →+* ℂ => f x) h

def realCoordinate (i : Fin places.count) :
    (enumeration E places i).Completion ≃+* ℝ :=
  ringEquivRealOfIsReal (IsTotallyReal.isReal (enumeration E places i))

theorem real_continuous (i : Fin places.count) : Continuous (realCoordinate E places i) :=
  (isometryEquivRealOfIsReal (IsTotallyReal.isReal (enumeration E places i))).continuous

theorem real_inverse_continuous (i : Fin places.count) :
    Continuous (realCoordinate E places i).symm :=
  (isometryEquivRealOfIsReal (IsTotallyReal.isReal (enumeration E places i))).symm.continuous

theorem rational (i : Fin places.count) (x : QuadraticConjugation.CM.Field.RealField E) :
    (realCoordinate E places i
      (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (QuadraticConjugation.CM.Field.RealField E) (.inl (enumeration E places i)) x) : ℂ) =
        ReferenceDatum.CM.embeddings E places i (x : E) := by
  change (extensionEmbeddingOfIsReal (IsTotallyReal.isReal (enumeration E places i))
    (algebraMap (QuadraticConjugation.CM.Field.RealField E) (enumeration E places i).Completion x) : ℂ) = _
  simpa using CM.embedding E places i x

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanPlaces.CM
