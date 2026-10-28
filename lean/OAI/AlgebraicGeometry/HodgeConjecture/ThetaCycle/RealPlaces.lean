import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ReferenceDatum
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.QuadraticModel

/-! # Real Places -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealPlaces.CM

noncomputable section

/-! ThetaCycle: the selected CM embedding representatives enumerate exactly
the infinite places of the actual maximal real subfield. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.InfinitePlace
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [IsCMField K] (places : HeckeCycles.GeometricSource.CM.Places K)

def sourceInfinitePlace (i : Fin places.count) : InfinitePlace K :=
  InfinitePlace.mk (HeckeCycles.ReferenceDatum.CM.embeddings K places i).toRingHom

theorem source_infinite_place_bijective : Function.Bijective (sourceInfinitePlace K places) := by
  have hc := HeckeCycles.ReferenceDatum.CM.embeddings_complete K places
  constructor
  · intro i j h
    rcases InfinitePlace.mk_eq_iff.mp h with he | he
    · have he' : HeckeCycles.ReferenceDatum.CM.embeddings K places i = HeckeCycles.ReferenceDatum.CM.embeddings K places j := by
        ext x
        exact DFunLike.congr_fun he x
      exact congrArg Prod.fst (hc.1 (a₁ := (i, false)) (a₂ := (j, false)) he')
    · have he' : ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (HeckeCycles.ReferenceDatum.CM.embeddings K places i) = HeckeCycles.ReferenceDatum.CM.embeddings K places j := by
        ext x
        exact DFunLike.congr_fun he x
      exact congrArg Prod.fst (hc.1 (a₁ := (i, true)) (a₂ := (j, false)) he')
  · intro w
    obtain ⟨⟨i, b⟩, hi⟩ := hc.2 w.embedding.toRatAlgHom
    refine ⟨i, ?_⟩
    cases b
    · change HeckeCycles.ReferenceDatum.CM.embeddings K places i = w.embedding.toRatAlgHom at hi
      exact (congrArg InfinitePlace.mk (congrArg AlgHom.toRingHom hi)).trans (mk_embedding w)
    · change ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (HeckeCycles.ReferenceDatum.CM.embeddings K places i) = w.embedding.toRatAlgHom at hi
      have hm := congrArg InfinitePlace.mk (congrArg AlgHom.toRingHom hi)
      change InfinitePlace.mk (ComplexEmbedding.conjugate (HeckeCycles.ReferenceDatum.CM.embeddings K places i).toRingHom) =
        InfinitePlace.mk w.embedding at hm
      rw [mk_conjugate_eq, mk_embedding] at hm
      exact hm

def sourceRealPlaces : Fin places.count ≃ InfinitePlace (maximalRealSubfield K) :=
  (Equiv.ofBijective (sourceInfinitePlace K places) (source_infinite_place_bijective K places)).trans
    (IsCMField.equivInfinitePlace K)

theorem source_real_place_restriction (i : Fin places.count) :
    sourceRealPlaces K places i =
      InfinitePlace.mk ((HeckeCycles.ReferenceDatum.CM.embeddings K places i).toRingHom.comp
        (algebraMap (maximalRealSubfield K) K)) := by
  rfl

theorem source_real_embedding (i : Fin places.count) (x : maximalRealSubfield K) :
    (embedding_of_isReal (IsTotallyReal.isReal (sourceRealPlaces K places i)) x : ℂ) =
      HeckeCycles.ReferenceDatum.CM.embeddings K places i (x : K) := by
  rw [embedding_of_isReal_apply]
  have h := InfinitePlace.embedding_mk_eq_of_isReal
    (IsTotallyReal.complexEmbedding_isReal
      ((HeckeCycles.ReferenceDatum.CM.embeddings K places i).toRingHom.comp (algebraMap (maximalRealSubfield K) K)))
  rw [← source_real_place_restriction] at h
  exact congrArg (fun f : maximalRealSubfield K →+* ℂ => f x) h

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealPlaces.CM
