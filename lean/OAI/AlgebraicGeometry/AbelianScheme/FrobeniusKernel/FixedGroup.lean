import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FixedGroupCover
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks

/-! # Fixed Group -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FixedGroup.Construction

noncomputable section

/-! The fixed subgroup of the actual idempotent cover is finite,
commutative, and closed, with its original inclusion retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) (e : G ⟶ G) (he : e ≫ e = e)

include he in
theorem fixedGroupInclusion_mono : Mono (FixedGroupCover.Construction.fixedGroupInclusion G e).hom.hom :=
  mono_of_mono_fac (congrArg (fun t : FixedGroupCover.Construction.fixedGroup G e ⟶ FixedGroupCover.Construction.fixedGroup G e => t.hom.hom)
    (FixedGroupCover.Construction.fixedGroupInclusion_retraction G e he))

include he in
theorem fixedGroup_finite [IsFinite G.X.hom] : IsFinite (FixedGroupCover.Construction.fixedGroup G e).X.hom :=
  CartierDuality.IntrinsicRetracts.Construction.Schemes.finite_of_over_retract (FixedGroupCover.Construction.fixedGroupInclusion G e).hom.hom
    (FixedGroupCover.Construction.fixedGroupRetraction G e he).hom.hom
    (congrArg (fun t : FixedGroupCover.Construction.fixedGroup G e ⟶ FixedGroupCover.Construction.fixedGroup G e => t.hom.hom)
      (FixedGroupCover.Construction.fixedGroupInclusion_retraction G e he))

include he in
theorem fixedGroupInclusion_closed [IsFinite G.X.hom] :
    IsClosedImmersion (FixedGroupCover.Construction.fixedGroupInclusion G e).hom.hom.left := by
  have : IsFinite (FixedGroupCover.Construction.fixedGroup G e).X.hom := fixedGroup_finite G e he
  have : Mono (FixedGroupCover.Construction.fixedGroupInclusion G e).hom.hom := fixedGroupInclusion_mono G e he
  exact OrdinaryBlocks.Construction.closedSubgroupOfFiniteMono (FixedGroupCover.Construction.fixedGroupInclusion G e).hom.hom

include he in
theorem fixedGroup_commutative [IsCommMonObj G.X] : IsCommMonObj (FixedGroupCover.Construction.fixedGroup G e).X := by
  have : Mono (FixedGroupCover.Construction.fixedGroupInclusion G e).hom.hom := fixedGroupInclusion_mono G e he
  apply (isCommMonObj_iff_isMulCommutative _).mpr
  intro T
  refine ⟨⟨fun x y => ?_⟩⟩
  apply (cancel_mono (FixedGroupCover.Construction.fixedGroupInclusion G e).hom.hom).mp
  rw [MonObj.mul_comp, MonObj.mul_comp, mul_comm]

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FixedGroup.Construction
