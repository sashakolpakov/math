import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.UniversalSubgroupEq

/-! # Universal Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.UniversalUniqueness.UniversalSubgroup

/-! Uniqueness of a classifying map for the actual universal subgroup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {H : Over S} [GrpObj H]
variable {M : Type u} [Group M] [Fintype M]
variable [IsFinite H.hom] [Etale H.hom] (D : Unmarked.UnmarkedQuotient.Data H M)

theorem classifying_injective {T : Over S} (f g : T ⟶ D.parameter)
    (h : (UniversalSubgroupEq.UniversalSubgroup.subgroup D).baseChange f = (UniversalSubgroupEq.UniversalSubgroup.subgroup D).baseChange g) : f = g := by
  have : Etale D.parameter.hom := D.etale
  apply IsogenyQuotient.Geometric.Points.Construction.etale_ext_of_geometric_points
  intro K hK hclosed s x
  have he := congrArg (fun F : SubgroupFunctor.RelativeSubgroup H T => F.points (Over.mk s) x) h
  change (UniversalSubgroupEq.UniversalSubgroup.subgroup D).points (Over.mk s) (x ≫ f) =
    (UniversalSubgroupEq.UniversalSubgroup.subgroup D).points (Over.mk s) (x ≫ g) at he
  rw [UniversalSubgroupEq.UniversalSubgroup.geometric_points_eq, UniversalSubgroupEq.UniversalSubgroup.geometric_points_eq] at he
  have hp := (MarkingRangesIff.MarkingRanges.same_projection_iff_range D K s
    (UniversalSubgroupEq.UniversalSubgroup.geometricMark D K s (x ≫ f)) (UniversalSubgroupEq.UniversalSubgroup.geometricMark D K s (x ≫ g))).mpr he
  exact (UniversalSubgroupEq.UniversalSubgroup.geometricMark_projection D K s (x ≫ f)).symm.trans
    (hp.trans (UniversalSubgroupEq.UniversalSubgroup.geometricMark_projection D K s (x ≫ g)))

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.UniversalUniqueness.UniversalSubgroup
