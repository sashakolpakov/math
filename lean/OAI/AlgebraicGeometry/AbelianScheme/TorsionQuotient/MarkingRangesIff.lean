import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Points
import Mathlib.Algebra.Group.Subgroup.Map

/-! # Marking Ranges Iff -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.MarkingRangesIff.MarkingRanges

/-! Removing a marking identifies exactly homomorphisms with the same subgroup image. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u v

theorem exists_reindex {M : Type u} {N : Type v} [Group M] [Group N]
    (a b : M →* N) (ha : Function.Injective a) (hb : Function.Injective b)
    (h : a.range = b.range) : ∃ σ : M ≃* M, a.comp σ.toMonoidHom = b := by
  let σ := (MonoidHom.ofInjective hb).trans
    ((MulEquiv.subgroupCongr h.symm).trans (MonoidHom.ofInjective ha).symm)
  refine ⟨σ, ?_⟩
  apply MonoidHom.ext
  intro m
  exact (MonoidHom.apply_ofInjective_symm ha _).trans (MonoidHom.ofInjective_apply hb)

variable {S : Scheme.{u}} {H : Over S} [GrpObj H]
variable {M : Type u} [Group M] [Fintype M]
variable [IsFinite H.hom] [Etale H.hom] (D : Unmarked.UnmarkedQuotient.Data H M)

theorem same_projection_iff_range (K : Type u) [Field K]
    (s : Spec (CommRingCat.of K) ⟶ S)
    (a b : Over.mk s ⟶ EmbeddingParametersIs.EmbeddingParameters.parameter H M) :
    a ≫ D.projection = b ≫ D.projection ↔
      (EmbeddingParametersIs.EmbeddingParameters.points H M _ a).val.range =
        (EmbeddingParametersIs.EmbeddingParameters.points H M _ b).val.range := by
  rw [Points.UnmarkedQuotient.same_projection_iff_orbit D K s a b]
  constructor
  · rintro ⟨σ, hσ⟩
    have h := congrArg (EmbeddingParametersIs.EmbeddingParameters.points H M _) hσ
    rw [MarkingActionOn.MarkingAction.points_comp_map] at h
    have he : (EmbeddingParametersIs.EmbeddingParameters.points H M _ a).val.comp σ.toMonoidHom =
        (EmbeddingParametersIs.EmbeddingParameters.points H M _ b).val := congrArg Subtype.val h
    have hr : σ.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr σ.surjective
    rw [← he, MonoidHom.range_comp, hr, ← MonoidHom.range_eq_map]
  · intro h
    have ha : Function.Injective (EmbeddingParametersIs.EmbeddingParameters.points H M _ a).val := by
      intro m n he
      apply (EmbeddingParametersIs.EmbeddingParameters.points H M _ a).property K s (𝟙 _)
      simpa only [Category.id_comp] using he
    have hb : Function.Injective (EmbeddingParametersIs.EmbeddingParameters.points H M _ b).val := by
      intro m n he
      apply (EmbeddingParametersIs.EmbeddingParameters.points H M _ b).property K s (𝟙 _)
      simpa only [Category.id_comp] using he
    obtain ⟨σ, hσ⟩ := exists_reindex _ _ ha hb h
    refine ⟨σ, ?_⟩
    apply EmbeddingParametersIs.EmbeddingParameters.points_injective H M
    rw [MarkingActionOn.MarkingAction.points_comp_map]
    exact Subtype.ext hσ

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.MarkingRangesIff.MarkingRanges
