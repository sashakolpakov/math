import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.EtaleSubgroup

/-! # Subgroup Detection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupDetection.EtaleSubgroupModels

/-! Equality of actual finite étale subgroup families from geometric fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {H T : Over S} [GrpObj H]
variable [IsFinite H.hom] [Etale H.hom]

theorem eq_of_geometric_points {F G : SubgroupFunctor.RelativeSubgroup H T} (R : F.Model) (R' : G.Model)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (s : Spec (CommRingCat.of K) ⟶ S) (t : Over.mk s ⟶ T),
      F.points (Over.mk s) t = G.points (Over.mk s) t) : F = G := by
  ext X t a
  rw [EtaleSubgroup.EtaleSubgroupModels.membership_iff_geometric R t a, EtaleSubgroup.EtaleSubgroupModels.membership_iff_geometric R' t a]
  constructor
  · intro ha K hK hclosed s x
    rw [← h K s (x ≫ t)]
    exact ha K s x
  · intro ha K hK hclosed s x
    rw [h K s (x ≫ t)]
    exact ha K s x

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupDetection.EtaleSubgroupModels
