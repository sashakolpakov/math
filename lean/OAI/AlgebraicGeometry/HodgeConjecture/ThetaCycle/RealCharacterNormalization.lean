import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.FieldAdelicCharacter
import OAI.RepresentationTheory.Weil.AdelicSplitting.Characters
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Algebra.Order.Archimedean.Real.Hom

/-! # Real Character Normalization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealCharacterNormalization.CM

noncomputable section

/-! ThetaCycle: exact standard-exponential normalization at every real place
of a totally real number field. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.InfinitePlace _root_.NumberField.InfinitePlace.Completion
open OAI.RepresentationTheory.Weil.AdelicSplitting.Characters.Construction

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

def realPlaceEmbeddingEquiv : InfinitePlace F ≃ (F →ₐ[ℚ] ℂ) :=
  (Equiv.ofBijective (InfinitePlace.embedding (K := F))
    ⟨InfinitePlace.embedding_injective F, fun φ =>
      ⟨InfinitePlace.mk φ,
        InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal φ)⟩⟩).trans
    (RingHom.equivRatAlgHom F ℂ)

theorem field_trace_real_places (q : F) :
    (Algebra.trace ℚ F q : ℝ) =
      ∑ v : InfinitePlace F, embedding_of_isReal (IsTotallyReal.isReal v) q := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  simp only [embedding_of_isReal_apply]
  change algebraMap ℚ ℂ (Algebra.trace ℚ F q) =
    ∑ v : InfinitePlace F, realPlaceEmbeddingEquiv F v q
  rw [trace_eq_sum_embeddings ℂ]
  exact (Equiv.sum_comp (realPlaceEmbeddingEquiv F) (fun σ : F →ₐ[ℚ] ℂ => σ q)).symm

theorem infinite_field_trace_real_places (a : InfiniteAdeleRing F) :
    ArchimedeanTrace.CM.infiniteFieldTrace F a =
      ∑ v : InfinitePlace F, extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (a v) := by
  have hc : Continuous (fun a : InfiniteAdeleRing F =>
      ∑ v : InfinitePlace F, extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (a v)) :=
    continuous_finsetSum _ (fun v _ =>
      (isometry_extensionEmbeddingOfIsReal (IsTotallyReal.isReal v)).continuous.comp
        (continuous_apply v))
  have he := (InfiniteAdeleRing.denseRange_algebraMap F).equalizer
    (ArchimedeanTrace.CM.infinite_field_trace_continuous F) hc (funext fun q => by
      change ArchimedeanTrace.CM.infiniteFieldTrace F (algebraMap F (InfiniteAdeleRing F) q) =
        ∑ v : InfinitePlace F, extensionEmbeddingOfIsReal (IsTotallyReal.isReal v)
          (algebraMap F v.Completion q)
      rw [ArchimedeanTrace.CM.infinite_field_trace_rational, field_trace_real_places]
      apply Finset.sum_congr rfl
      intro v _
      simp)
  exact congrFun he a

theorem infinite_field_trace_real_single (v : InfinitePlace F) (t : v.Completion) :
    ArchimedeanTrace.CM.infiniteFieldTrace F (Pi.single v t) =
      extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) t := by
  calc
    ArchimedeanTrace.CM.infiniteFieldTrace F (Pi.single v t) =
        ∑ w : InfinitePlace F, extensionEmbeddingOfIsReal (IsTotallyReal.isReal w) (Pi.single v t w) :=
      infinite_field_trace_real_places F _
    _ = extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) t := ?_
  rw [Finset.sum_eq_single v]
  · rw [Pi.single_eq_same]
  · intro w _ hw
    rw [Pi.single_eq_of_ne hw, map_zero]
  · simp

theorem field_adelic_character_standard_real (v : InfinitePlace F) (t : ℝ) :
    RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F (FieldAdelicCharacter.CM.fieldAdelicCharacter F) (.inl v)
      ((ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm t) =
        Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)) := by
  refine (FieldAdelicCharacter.CM.field_adelic_character_infinite F _).trans ?_
  refine (congrArg RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (infinite_field_trace_real_single F v _)).trans ?_
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter
    (ringEquivRealOfIsReal (IsTotallyReal.isReal v)
      ((ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm t)) = _
  rw [RingEquiv.apply_symm_apply, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter_apply]
  congr 1
  push_cast
  ring

omit [NumberField F] in
theorem real_completion_coordinate_unique (v : InfinitePlace F) (e : v.Completion ≃+* ℝ) :
    e = ringEquivRealOfIsReal (IsTotallyReal.isReal v) := by
  ext x
  have h := Real.ringHom_apply
    ((ringEquivRealOfIsReal (IsTotallyReal.isReal v)).toRingHom.comp e.symm.toRingHom) (e x)
  change ringEquivRealOfIsReal (IsTotallyReal.isReal v) (e.symm (e x)) = e x at h
  rw [RingEquiv.symm_apply_apply] at h
  exact h.symm

theorem field_adelic_character_standard_real_coordinate (v : InfinitePlace F)
    (e : v.Completion ≃+* ℝ) (t : ℝ) :
    RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F (FieldAdelicCharacter.CM.fieldAdelicCharacter F) (.inl v) (e.symm t) =
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)) := by
  rw [real_completion_coordinate_unique F v e]
  exact field_adelic_character_standard_real F v t

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealCharacterNormalization.CM
