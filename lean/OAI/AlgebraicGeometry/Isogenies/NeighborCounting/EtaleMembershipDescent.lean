import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupDetection

/-! # Etale Membership Descent -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleMembershipDescent

/-! Membership in the original finite etale subgroup descends along
a surjective change of test scheme. This recovers evaluated-field
membership from its actual geometric extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupDetection.EtaleSubgroupModels

universe u

variable {S : Scheme.{u}} {H P : Over S} [GrpObj H]
  [IsFinite H.hom] [Etale H.hom]
  {F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup H P} (R : F.Model)

include R in
theorem membership_iff_surjective {X Y : Over S} (f : Y ⟶ X)
    [Surjective f.left] (t : X ⟶ P) (a : X ⟶ H) :
    a ∈ F.points X t ↔ f ≫ a ∈ F.points Y (f ≫ t) := by
  constructor
  · exact F.naturality f t
  · intro ha
    have hr := (AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.membership_iff_range R (f ≫ t) (f ≫ a)).mp ha
    apply (AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.membership_iff_range R t a).mpr
    rintro z ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := (inferInstance : Surjective f.left).surj x
    have h := hr ⟨y, rfl⟩
    rw [← comp_lift] at h
    change (lift t a).left (f.left y) ∈ Set.range (AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.inclusion R).left at h
    rwa [hy] at h

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleMembershipDescent
