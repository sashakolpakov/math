import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Unmarked
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.Points

/-! # Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Points.UnmarkedQuotient

/-! The geometric points of the constructed quotient are unmarked subgroups. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {H : Over S} [GrpObj H]
variable {M : Type u} [Group M] [Fintype M]
variable [IsFinite H.hom] [Etale H.hom] (D : Unmarked.UnmarkedQuotient.Data H M)

theorem invariant (σ : M ≃* M) :
    MarkingActionOn.MarkingAction.map H M σ ≫ D.projection = D.projection := by
  have he : FreeConstant.FreeConstantAction.source ≫ D.projection =
      FreeConstant.FreeConstantAction.target (Unmarked.UnmarkedQuotient.action H M) ≫ D.projection :=
    Over.OverMorphism.ext D.kernelPair.w
  have hi := congrArg (fun f => FreeConstant.FreeConstantAction.inclusion σ ≫ f) he
  simpa only [← Category.assoc, FreeConstant.FreeConstantAction.inclusion_source,
    FreeConstant.FreeConstantAction.inclusion_target, Category.id_comp, Unmarked.UnmarkedQuotient.action] using hi.symm

theorem same_projection_iff_orbit (K : Type u) [Field K]
    (s : Spec (CommRingCat.of K) ⟶ S)
    (a b : Over.mk s ⟶ EmbeddingParametersIs.EmbeddingParameters.parameter H M) :
    a ≫ D.projection = b ≫ D.projection ↔
      ∃ σ : M ≃* M, a ≫ MarkingActionOn.MarkingAction.map H M σ = b := by
  constructor
  · intro hab
    let z₀ := D.kernelPair.lift a.left b.left (congrArg (fun f => f.left) hab)
    have hzbase : z₀ ≫
        (FreeConstant.FreeConstantAction.relation (X := EmbeddingParametersIs.EmbeddingParameters.parameter H M)
          (G := M ≃* M)).hom = s := by
      rw [← (FreeConstant.FreeConstantAction.source (X := EmbeddingParametersIs.EmbeddingParameters.parameter H M)
        (G := M ≃* M)).w, ← Category.assoc]
      exact (congrArg (fun f => f ≫ (EmbeddingParametersIs.EmbeddingParameters.parameter H M).hom)
        (D.kernelPair.lift_fst _ _ _)).trans a.w
    let z : Over.mk s ⟶ FreeConstant.FreeConstantAction.relation := Over.homMk z₀ hzbase
    have hs : z ≫ FreeConstant.FreeConstantAction.source = a :=
      Over.OverMorphism.ext (D.kernelPair.lift_fst _ _ _)
    have ht : z ≫ FreeConstant.FreeConstantAction.target (Unmarked.UnmarkedQuotient.action H M) = b :=
      Over.OverMorphism.ext (D.kernelPair.lift_snd _ _ _)
    obtain ⟨σ, hz⟩ := FreeConstant.FreeConstantAction.field_factor K s z
    refine ⟨σ, ?_⟩
    have he := congrArg (fun f => f ≫ FreeConstant.FreeConstantAction.target (Unmarked.UnmarkedQuotient.action H M)) hz
    rw [Category.assoc, FreeConstant.FreeConstantAction.inclusion_target, hs, ht] at he
    exact he.symm
  · rintro ⟨σ, hσ⟩
    rw [← hσ, Category.assoc, invariant D]

theorem geometric_surjective (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) :
    Function.Surjective (fun a : Over.mk s ⟶ EmbeddingParametersIs.EmbeddingParameters.parameter H M =>
      a ≫ D.projection) := by
  let : Surjective D.projection.left := D.projection_surjective
  let : IsFinite D.projection.left := D.projection_finite
  exact IsogenyQuotient.Geometric.Points.Construction.surjective_on_geometric_points D.projection K s

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Points.UnmarkedQuotient
