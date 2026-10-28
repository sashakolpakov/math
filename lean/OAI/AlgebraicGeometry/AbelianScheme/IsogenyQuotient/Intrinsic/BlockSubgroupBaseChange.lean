import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.BlockBaseChangeGroup
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ParameterSubgroupTransport

/-! # Block Subgroup Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.BlockSubgroupBaseChange.Construction

noncomputable section

/-! Native block inclusions identify the original subgroup's parameter
pullback with its inverse image or image on the actual new torsion block. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (P : Over S)
  (p : A.scheme ⟶ A.scheme) [IsMonHom p] (n : ℕ)

set_option backward.isDefEq.respectTransparency false in
theorem parameter_nativeBlock_subgroup_comparison (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme P) :
    SubgroupTransport.Construction.relativeSubgroupPullback (BlockBaseChangeGroup.Construction.nativeBlockBaseChangeIso A p n P.hom).hom
      (Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk (OppositeKernel.Construction.torsionBlock n p)) P
        (SubgroupTransport.Construction.relativeSubgroupPullback (OppositeKernel.Construction.torsionBlockInclusion n p) F)) =
      SubgroupTransport.Construction.relativeSubgroupPullback (OppositeKernel.Construction.torsionBlockInclusion n ((Over.pullback P.hom).map p))
        (Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk A.scheme) P F) := by
  have hp := ParameterSubgroupTransport.Construction.relativeSubgroupOverParameter_pullback (Grp.mk A.scheme) (Grp.mk (OppositeKernel.Construction.torsionBlock n p)) P
    (Grp.homMk (OppositeKernel.Construction.torsionBlockInclusion n p)) F
  exact (congrArg (SubgroupTransport.Construction.relativeSubgroupPullback (BlockBaseChangeGroup.Construction.nativeBlockBaseChangeIso A p n P.hom).hom) hp).trans
    (ParameterSubgroupTransport.Construction.relativeSubgroupPullback_iso_square (BlockBaseChangeGroup.Construction.nativeBlockBaseChangeIso A p n P.hom)
      ((Over.pullback P.hom).map (OppositeKernel.Construction.torsionBlockInclusion n p))
      (OppositeKernel.Construction.torsionBlockInclusion n ((Over.pullback P.hom).map p))
      (BlockBaseChangeGroup.Construction.nativeBlockBaseChangeIso_hom_inclusion A p n P.hom)
      (Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk A.scheme) P F))

set_option backward.isDefEq.respectTransparency false in
theorem parameter_nativeBlock_image_comparison (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup (OppositeKernel.Construction.torsionBlock n p) P) :
    Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk A.scheme) P (SubgroupTransport.Construction.relativeSubgroupImage (OppositeKernel.Construction.torsionBlockInclusion n p) F) =
      SubgroupTransport.Construction.relativeSubgroupImage (OppositeKernel.Construction.torsionBlockInclusion n ((Over.pullback P.hom).map p))
        (SubgroupTransport.Construction.relativeSubgroupPullback (BlockBaseChangeGroup.Construction.nativeBlockBaseChangeIso A p n P.hom).hom
          (Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk (OppositeKernel.Construction.torsionBlock n p)) P F)) := by
  exact (ParameterSubgroupTransport.Construction.relativeSubgroupOverParameter_image (Grp.mk A.scheme) (Grp.mk (OppositeKernel.Construction.torsionBlock n p)) P
    (Grp.homMk (OppositeKernel.Construction.torsionBlockInclusion n p)) F).trans
    (ParameterSubgroupTransport.Construction.relativeSubgroupImage_iso_square (BlockBaseChangeGroup.Construction.nativeBlockBaseChangeIso A p n P.hom)
      ((Over.pullback P.hom).map (OppositeKernel.Construction.torsionBlockInclusion n p))
      (OppositeKernel.Construction.torsionBlockInclusion n ((Over.pullback P.hom).map p))
      (BlockBaseChangeGroup.Construction.nativeBlockBaseChangeIso_hom_inclusion A p n P.hom)
      (Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk (OppositeKernel.Construction.torsionBlock n p)) P F)).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.BlockSubgroupBaseChange.Construction
