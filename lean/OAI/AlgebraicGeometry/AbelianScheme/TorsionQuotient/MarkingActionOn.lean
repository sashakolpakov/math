import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.EmbeddingParametersIs

/-! # Marking Action On -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.MarkingActionOn.MarkingAction

/-! Automorphisms of the label group act on the actual embedding scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} (H : Over S) [GrpObj H]
variable (M : Type u) [Group M] [Fintype M]
variable [IsFinite H.hom] [Etale H.hom]

noncomputable def reindex {T : Over S} (a : EmbeddingParametersIs.EmbeddingParameters.Choice H M T)
    (σ : M ≃* M) : EmbeddingParametersIs.EmbeddingParameters.Choice H M T :=
  ⟨a.val.comp σ.toMonoidHom, by
    intro K hK s t x y hxy
    exact σ.injective (a.property K s t hxy)⟩

noncomputable def map (σ : M ≃* M) :
    EmbeddingParametersIs.EmbeddingParameters.parameter H M ⟶ EmbeddingParametersIs.EmbeddingParameters.parameter H M :=
  (EmbeddingParametersIs.EmbeddingParameters.pointsEquiv H M _).symm
    (reindex H M (EmbeddingParametersIs.EmbeddingParameters.points H M _ (𝟙 _)) σ)

theorem points_map (σ : M ≃* M) :
    EmbeddingParametersIs.EmbeddingParameters.points H M _ (map H M σ) =
      reindex H M (EmbeddingParametersIs.EmbeddingParameters.points H M _ (𝟙 _)) σ :=
  (EmbeddingParametersIs.EmbeddingParameters.pointsEquiv H M _).apply_symm_apply _

theorem points_comp_map {T : Over S} (a : T ⟶ EmbeddingParametersIs.EmbeddingParameters.parameter H M)
    (σ : M ≃* M) :
    EmbeddingParametersIs.EmbeddingParameters.points H M T (a ≫ map H M σ) =
      reindex H M (EmbeddingParametersIs.EmbeddingParameters.points H M T a) σ := by
  have hn := (EmbeddingParametersIs.EmbeddingParameters.representable H M).homEquiv_comp a (map H M σ)
  change EmbeddingParametersIs.EmbeddingParameters.points H M T (a ≫ map H M σ) =
    EmbeddingParametersIs.EmbeddingParameters.baseChange H M
      (EmbeddingParametersIs.EmbeddingParameters.points H M _ (map H M σ)) a at hn
  rw [hn]
  rw [points_map]
  apply Subtype.ext
  apply MonoidHom.ext
  intro m
  change a ≫ ((𝟙 _ ≫ EmbeddingParametersIs.EmbeddingParameters.inclusion H M) ≫
      HomParametersMul.HomParameters.coefficient H M (σ m)) =
    (a ≫ EmbeddingParametersIs.EmbeddingParameters.inclusion H M) ≫ HomParametersMul.HomParameters.coefficient H M (σ m)
  simp only [Category.id_comp, Category.assoc]

@[simp]
theorem map_refl : map H M (MulEquiv.refl M) = 𝟙 _ := by
  apply EmbeddingParametersIs.EmbeddingParameters.points_injective H M
  rw [points_map]
  rfl

theorem map_comp (σ τ : M ≃* M) :
    map H M σ ≫ map H M τ = map H M (τ.trans σ) := by
  apply EmbeddingParametersIs.EmbeddingParameters.points_injective H M
  rw [points_comp_map, points_map, points_map]
  rfl

noncomputable def iso (σ : M ≃* M) :
    EmbeddingParametersIs.EmbeddingParameters.parameter H M ≅ EmbeddingParametersIs.EmbeddingParameters.parameter H M where
  hom := map H M σ
  inv := map H M σ.symm
  hom_inv_id := by rw [map_comp]; simp
  inv_hom_id := by rw [map_comp]; simp

/-- Reindexing a field-valued embedding is a free action. -/
theorem free_on_field_points (K : Type u) [Field K]
    (s : Spec (CommRingCat.of K) ⟶ S)
    (a : Over.mk s ⟶ EmbeddingParametersIs.EmbeddingParameters.parameter H M) (σ τ : M ≃* M)
    (h : a ≫ map H M σ = a ≫ map H M τ) : σ = τ := by
  have he := congrArg (EmbeddingParametersIs.EmbeddingParameters.points H M _) h
  rw [points_comp_map, points_comp_map] at he
  apply MulEquiv.ext
  intro m
  apply (EmbeddingParametersIs.EmbeddingParameters.points H M _ a).property K s (𝟙 _)
  simpa only [reindex, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Category.id_comp] using
    congrArg (fun c : EmbeddingParametersIs.EmbeddingParameters.Choice H M (Over.mk s) => c.val m) he

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.MarkingActionOn.MarkingAction
