import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.AdelicCharacter
import OAI.RepresentationTheory.Weil.AdelicSplitting.Characters

/-! # Character Normalization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.CharacterNormalization.CM

noncomputable section

/-! The constructed number-field character is exactly the standard
exponential at every real place of a totally real field. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.InfinitePlace _root_.NumberField.InfinitePlace.Completion
open OAI.RepresentationTheory.Weil.AdelicSplitting.Characters.Construction

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

def embeddingEquiv : InfinitePlace F ≃ (F →ₐ[ℚ] ℂ) :=
  (Equiv.ofBijective (InfinitePlace.embedding (K := F))
    ⟨InfinitePlace.embedding_injective F, fun φ =>
      ⟨InfinitePlace.mk φ,
        InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal φ)⟩⟩).trans
    (RingHom.equivRatAlgHom F ℂ)

theorem trace_places (x : F) : (Algebra.trace ℚ F x : ℝ) =
    ∑ v : InfinitePlace F, embedding_of_isReal (IsTotallyReal.isReal v) x := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  simp only [embedding_of_isReal_apply]
  change algebraMap ℚ ℂ (Algebra.trace ℚ F x) = ∑ v : InfinitePlace F, embeddingEquiv F v x
  rw [trace_eq_sum_embeddings ℂ]
  exact (Equiv.sum_comp (embeddingEquiv F) (fun σ : F →ₐ[ℚ] ℂ => σ x)).symm

theorem adelic_trace (a : InfiniteAdeleRing F) : ArchimedeanTrace.CM.trace F a =
    ∑ v : InfinitePlace F, extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (a v) := by
  have hc : Continuous (fun a : InfiniteAdeleRing F =>
      ∑ v : InfinitePlace F, extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (a v)) :=
    continuous_finsetSum _ (fun v _ =>
      (isometry_extensionEmbeddingOfIsReal (IsTotallyReal.isReal v)).continuous.comp (continuous_apply v))
  have he := (InfiniteAdeleRing.denseRange_algebraMap F).equalizer
    (ArchimedeanTrace.CM.trace_continuous F) hc (funext fun x => by
      change ArchimedeanTrace.CM.trace F (algebraMap F (InfiniteAdeleRing F) x) =
        ∑ v : InfinitePlace F, extensionEmbeddingOfIsReal (IsTotallyReal.isReal v)
          (algebraMap F v.Completion x)
      rw [ArchimedeanTrace.CM.trace_rational, trace_places]
      apply Finset.sum_congr rfl
      intro v _
      simp)
  exact congrFun he a

theorem single_trace (v : InfinitePlace F) (t : v.Completion) :
    ArchimedeanTrace.CM.trace F (Pi.single v t) =
      extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) t := by
  calc
    ArchimedeanTrace.CM.trace F (Pi.single v t) =
        ∑ w : InfinitePlace F, extensionEmbeddingOfIsReal (IsTotallyReal.isReal w) (Pi.single v t w) :=
      adelic_trace F _
    _ = extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) t := ?_
  rw [Finset.sum_eq_single v]
  · rw [Pi.single_eq_same]
  · intro w _ hw
    rw [Pi.single_eq_of_ne hw, map_zero]
  · simp

theorem standard_real (v : InfinitePlace F) (t : ℝ) :
    RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F (HeckeCycles.NumberField.AdelicCharacter.CM.character F) (.inl v)
      ((ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm t) =
        Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)) := by
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (ArchimedeanTrace.CM.trace F (Pi.single v _)) *
    HeckeCycles.NumberField.FiniteCharacter.CM.character F 0 = _
  rw [AddChar.map_zero_eq_one, mul_one, single_trace]
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter
    (ringEquivRealOfIsReal (IsTotallyReal.isReal v)
      ((ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm t)) = _
  rw [RingEquiv.apply_symm_apply, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter_apply]
  congr 1
  push_cast
  ring

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.CharacterNormalization.CM
