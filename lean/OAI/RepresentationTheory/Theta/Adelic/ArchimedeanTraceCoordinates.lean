import OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.RingTheory.Trace.Basic

/-! # Archimedean Trace Coordinates -/

namespace OAI.RepresentationTheory.Theta.Adelic.ArchimedeanTraceCoordinates

noncomputable section

/-! The displayed real embeddings sum to the actual rational field trace. -/

open scoped Classical _root_.NumberField

open _root_.NumberField _root_.NumberField.InfinitePlace
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.TotallyRealData

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

theorem real_coordinate_unique (v : Fin A.places) :
    A.real v = Completion.ringEquivRealOfIsReal (TotallyRealData.displayed_place_real A v) := by
  ext x
  have h := Real.ringHom_apply
    ((Completion.ringEquivRealOfIsReal (TotallyRealData.displayed_place_real A v)).toRingHom.comp
      (A.real v).symm.toRingHom) (A.real v x)
  change Completion.ringEquivRealOfIsReal (TotallyRealData.displayed_place_real A v)
    ((A.real v).symm (A.real v x)) = A.real v x at h
  rw [RingEquiv.symm_apply_apply] at h
  exact h.symm

def displayedEmbeddingEquiv : Fin A.places ≃ (F →ₐ[ℚ] ℂ) := by
  let : NumberField.IsTotallyReal F := TotallyRealData.arithmetic_totally_real A
  exact A.enumerate.trans ((Equiv.ofBijective (InfinitePlace.embedding (K := F))
    ⟨InfinitePlace.embedding_injective F, fun φ =>
      ⟨InfinitePlace.mk φ,
        InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal φ)⟩⟩).trans
      (RingHom.equivRatAlgHom F ℂ))

theorem real_rational_embedding (v : Fin A.places) (q : F) :
    (A.real v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) q) : ℂ) =
      displayedEmbeddingEquiv A v q := by
  rw [real_coordinate_unique]
  change (Completion.extensionEmbeddingOfIsReal (TotallyRealData.displayed_place_real A v)
    (algebraMap F (A.enumerate v).Completion q) : ℂ) = (A.enumerate v).embedding q
  simp [embedding_of_isReal_apply]

theorem trace_eq_sum_real_coordinates (q : F) :
    (Algebra.trace ℚ F q : ℝ) =
      ∑ v : Fin A.places, A.real v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) q) := by
  apply Complex.ofReal_injective
  calc
    ((Algebra.trace ℚ F q : ℝ) : ℂ) =
        ∑ σ : F →ₐ[ℚ] ℂ, σ q := by
      simpa using (trace_eq_sum_embeddings ℂ (K := ℚ) (L := F) (x := q))
    _ = ∑ v : Fin A.places, displayedEmbeddingEquiv A v q :=
      (Equiv.sum_comp (displayedEmbeddingEquiv A) (fun σ : F →ₐ[ℚ] ℂ => σ q)).symm
    _ = ∑ v : Fin A.places,
        (A.real v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) q) : ℂ) :=
      Finset.sum_congr rfl (fun v _ => (real_rational_embedding A v q).symm)
    _ = _ := (Complex.ofReal_sum _ _).symm

end

end OAI.RepresentationTheory.Theta.Adelic.ArchimedeanTraceCoordinates
