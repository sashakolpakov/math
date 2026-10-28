import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.BlockBaseChangePoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionReferencePoint

/-! # Block Reference Torsion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.BlockReferenceTorsion.Construction

noncomputable section

/-! The original point of a native torsion block agrees with the
original torsion point after its actual fixed-point inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S S' : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (p : A.scheme ⟶ A.scheme) [IsMonHom p] (n : ℕ) (b : S' ⟶ S)

set_option backward.isDefEq.respectTransparency false in
theorem nativeBlockOriginalPoint_torsion (U : Over S')
    (x : U ⟶ OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)) :
    TorsionReferencePoint.Construction.nativeTorsionOriginalPoint b (Grp.mk A.scheme) n U
      (x ≫ BlockGroups.Construction.fixedPointInclusion (Torsion.Groups.Construction.nativeTorsionMap n ((Over.pullback b).map p))) =
        BlockBaseChangePoints.Construction.nativeBlockOriginalPoint A p n b U x ≫ BlockGroups.Construction.fixedPointInclusion (Torsion.Groups.Construction.nativeTorsionMap n p) := by
  apply (cancel_mono (Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n)).mp
  calc
    _ = (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b (Grp.mk A.scheme) U).symm
        ((x ≫ BlockGroups.Construction.fixedPointInclusion (Torsion.Groups.Construction.nativeTorsionMap n ((Over.pullback b).map p))) ≫
          Torsion.Groups.Construction.nativeTorsionInclusion ((Over.pullback b).obj A.scheme) n) :=
      TorsionReferencePoint.Construction.nativeTorsionOriginalPoint_inclusion b (Grp.mk A.scheme) n U _
    _ = A.baseChangePointsMulEquiv b U (x ≫ OppositeKernel.Construction.torsionBlockInclusion n ((Over.pullback b).map p)) :=
      congrArg (A.baseChangePointsMulEquiv b U)
        (Category.assoc x (BlockGroups.Construction.fixedPointInclusion (Torsion.Groups.Construction.nativeTorsionMap n ((Over.pullback b).map p)))
          (Torsion.Groups.Construction.nativeTorsionInclusion ((Over.pullback b).obj A.scheme) n))
    _ = BlockBaseChangePoints.Construction.nativeBlockOriginalPoint A p n b U x ≫ OppositeKernel.Construction.torsionBlockInclusion n p :=
      (BlockBaseChangePoints.Construction.nativeBlockOriginalPoint_inclusion A p n b U x).symm
    _ = _ := (Category.assoc (BlockBaseChangePoints.Construction.nativeBlockOriginalPoint A p n b U x)
      (BlockGroups.Construction.fixedPointInclusion (Torsion.Groups.Construction.nativeTorsionMap n p)) (Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n)).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.BlockReferenceTorsion.Construction
