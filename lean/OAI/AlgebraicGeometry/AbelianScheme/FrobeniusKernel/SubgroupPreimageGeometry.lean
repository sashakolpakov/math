import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SubgroupPreimage

/-! # Subgroup Preimage Geometry -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SubgroupPreimageGeometry.Construction

noncomputable section

/-! The subgroup preimage is a finite commutative group scheme when
its target subgroup is finite and its original source is commutative. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {A B J : Grp (Over S)} (f : A ⟶ B) (j : J ⟶ B)

instance subgroupPreimage_finite [IsFinite f.hom.hom.left] [IsFinite J.X.hom] :
    IsFinite (SubgroupPreimage.Construction.subgroupPreimage f j).X.hom := by
  have : IsFinite (SubgroupPreimage.Construction.subgroupPreimageProjection f j).hom.hom.left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (SubgroupPreimage.Construction.subgroupPreimage_geometricPullback f j) inferInstance
  have h : IsFinite ((SubgroupPreimage.Construction.subgroupPreimageProjection f j).hom.hom.left ≫ J.X.hom) := inferInstance
  exact (congrArg IsFinite (SubgroupPreimage.Construction.subgroupPreimageProjection f j).hom.hom.w).mp h

instance subgroupPreimage_commutative [IsCommMonObj A.X] [Mono j.hom.hom] :
    IsCommMonObj (SubgroupPreimage.Construction.subgroupPreimage f j).X := by
  apply (isCommMonObj_iff_isMulCommutative _).mpr
  intro T
  refine ⟨⟨fun x y => ?_⟩⟩
  apply (cancel_mono (SubgroupPreimage.Construction.subgroupPreimageInclusion f j).hom.hom).mp
  rw [MonObj.mul_comp, MonObj.mul_comp, mul_comm]

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SubgroupPreimageGeometry.Construction
