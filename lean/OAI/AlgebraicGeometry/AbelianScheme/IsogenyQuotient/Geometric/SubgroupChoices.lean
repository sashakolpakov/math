import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.UniversalSubgroupEq
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.Points

/-! # Subgroup Choices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.SubgroupChoices.Construction

noncomputable section

/-!
The geometric points of TorsionQuotient's actual unmarked subgroup parameter scheme
are exactly abstract subgroups of the prescribed type. Injective markings
over a field remain injective on every field-valued test point, and their
quotient identifies precisely equal subgroup images.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

theorem field_scheme_morphism_epi {K L : Type u} [Field K] [Field L]
    (f : Spec (.of L) ⟶ Spec (.of K)) : Epi f := by
  let a : CommRingCat.of K ⟶ CommRingCat.of L := Spec.preimage f
  have ha : Spec.map a = f := Spec.map_preimage f
  have : Epi (Spec.map a) := Points.Construction.field_spec_epi a.hom
  rwa [ha] at this

theorem field_marking_distinct {S : Scheme.{u}} (H : Over S) [GrpObj H]
    (M : Type u) [Group M] [Fintype M]
    {K : Type u} [Field K] (b : Spec (.of K) ⟶ S)
    (a : M →* (Over.mk b ⟶ H)) (ha : Function.Injective a) :
    TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.Distinct H M a := by
  intro L _ s t x y hxy
  have : Epi t.left := field_scheme_morphism_epi t.left
  have : Epi t := Over.epi_of_epi_left t
  exact ha ((cancel_epi t).mp hxy)

variable {S : Scheme.{u}} {H : Over S} [GrpObj H]
  {M : Type u} [Group M] [Fintype M] [IsFinite H.hom] [Etale H.hom]
  (D : TorsionQuotient.Unmarked.UnmarkedQuotient.Data H M)
  (K : Type u) [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ S)

def geometricSubgroupPoint (t : Over.mk b ⟶ D.parameter) :
    {J : Subgroup (Over.mk b ⟶ H) // Nonempty (J ≃* M)} :=
  ⟨(TorsionQuotient.UniversalSubgroupEq.UniversalSubgroup.subgroup D).points (Over.mk b) t,
    ⟨TorsionQuotient.UniversalSubgroupEq.UniversalSubgroup.geometricType D K b t⟩⟩

theorem geometricSubgroupPoint_injective : Function.Injective (geometricSubgroupPoint D K b) := by
  intro t v he
  have hgroups := congrArg Subtype.val he
  change (TorsionQuotient.UniversalSubgroupEq.UniversalSubgroup.subgroup D).points (Over.mk b) t =
    (TorsionQuotient.UniversalSubgroupEq.UniversalSubgroup.subgroup D).points (Over.mk b) v at hgroups
  rw [TorsionQuotient.UniversalSubgroupEq.UniversalSubgroup.geometric_points_eq, TorsionQuotient.UniversalSubgroupEq.UniversalSubgroup.geometric_points_eq] at hgroups
  have hp := (TorsionQuotient.MarkingRangesIff.MarkingRanges.same_projection_iff_range D K b
    (TorsionQuotient.UniversalSubgroupEq.UniversalSubgroup.geometricMark D K b t)
    (TorsionQuotient.UniversalSubgroupEq.UniversalSubgroup.geometricMark D K b v)).mpr hgroups
  simpa only [TorsionQuotient.UniversalSubgroupEq.UniversalSubgroup.geometricMark_projection] using hp

theorem geometricSubgroupPoint_surjective : Function.Surjective (geometricSubgroupPoint D K b) := by
  rintro ⟨J, ⟨e⟩⟩
  let a : M →* (Over.mk b ⟶ H) := J.subtype.comp e.symm.toMonoidHom
  have ha : Function.Injective a := J.subtype_injective.comp e.symm.injective
  let marking : TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.Choice H M (Over.mk b) :=
    ⟨a, field_marking_distinct H M b a ha⟩
  let p := (TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.pointsEquiv H M (Over.mk b)).symm marking
  let t := p ≫ D.projection
  refine ⟨t, Subtype.ext ?_⟩
  change (TorsionQuotient.UniversalSubgroupEq.UniversalSubgroup.subgroup D).points (Over.mk b) t = J
  rw [TorsionQuotient.UniversalSubgroupEq.UniversalSubgroup.geometric_points_eq]
  have hp := (TorsionQuotient.MarkingRangesIff.MarkingRanges.same_projection_iff_range D K b
    (TorsionQuotient.UniversalSubgroupEq.UniversalSubgroup.geometricMark D K b t) p).mp
      (TorsionQuotient.UniversalSubgroupEq.UniversalSubgroup.geometricMark_projection D K b t)
  have hm : TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.points H M (Over.mk b) p = marking :=
    (TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.pointsEquiv H M (Over.mk b)).apply_symm_apply marking
  change (TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.points H M (Over.mk b)
    (TorsionQuotient.UniversalSubgroupEq.UniversalSubgroup.geometricMark D K b t)).val.range = J
  rw [hp, hm]
  change a.range = J
  ext x
  constructor
  · rintro ⟨m, rfl⟩
    exact (e.symm m).property
  · intro hx
    exact ⟨e ⟨x, hx⟩, congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)⟩

/-- TorsionQuotient's geometric parameter points classify unmarked subgroup images
of the required abstract group type. -/
def geometricSubgroupPointEquiv :
    (Over.mk b ⟶ D.parameter) ≃ {J : Subgroup (Over.mk b ⟶ H) // Nonempty (J ≃* M)} :=
  Equiv.ofBijective (geometricSubgroupPoint D K b)
    ⟨geometricSubgroupPoint_injective D K b, geometricSubgroupPoint_surjective D K b⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.SubgroupChoices.Construction
