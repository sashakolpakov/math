import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.MarkingActionOn
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Action
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Finite

/-! # Unmarked -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Unmarked.UnmarkedQuotient

/-! The finite étale quotient of the scheme of injective markings. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (H : Over S) [GrpObj H]
variable (M : Type u) [Group M] [Fintype M]
variable [IsFinite H.hom] [Etale H.hom]

noncomputable def action : FreeConstant.FreeConstantAction.Data (EmbeddingParametersIs.EmbeddingParameters.parameter H M) (M ≃* M) where
  map := MarkingActionOn.MarkingAction.map H M
  map_one := MarkingActionOn.MarkingAction.map_refl H M
  map_mul σ τ := MarkingActionOn.MarkingAction.map_comp H M σ τ
  free := MarkingActionOn.MarkingAction.free_on_field_points H M

structure Data where
  parameter : Over S
  projection : EmbeddingParametersIs.EmbeddingParameters.parameter H M ⟶ parameter
  finite : IsFinite parameter.hom
  etale : Etale parameter.hom
  projection_finite : IsFinite projection.left
  projection_etale : Etale projection.left
  projection_surjective : Surjective projection.left
  kernelPair : IsKernelPair projection.left
    (FreeConstant.FreeConstantAction.source (X := EmbeddingParametersIs.EmbeddingParameters.parameter H M) (G := M ≃* M)).left
    (FreeConstant.FreeConstantAction.target (action H M)).left

/-- The quotient and both finite étale morphisms are constructed from the
original finite étale group scheme and the finite label group. -/
theorem exists_data : Nonempty (Data H M) := by
  obtain ⟨Q, q, hf, hfl, hfp, hsurj, hk⟩ :=
    Action.FreeConstantAction.exists_quotient (action H M)
  let := hf
  let := hfl
  let := hfp
  let := hsurj
  have : IsFinite (q.left ≫ Q.hom) := by rw [q.w]; infer_instance
  have : Etale (q.left ≫ Q.hom) := by rw [q.w]; infer_instance
  obtain ⟨hQf, hQe⟩ := Finite.FiniteQuotientGeometry.finite_etale_of_finite_flat_cover q.left Q.hom
  let := hQe
  exact ⟨⟨Q, q, hQf, hQe, hf, Etale.of_comp q.left Q.hom, hsurj, hk⟩⟩

noncomputable def constructed : Data H M := (exists_data H M).some

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Unmarked.UnmarkedQuotient
