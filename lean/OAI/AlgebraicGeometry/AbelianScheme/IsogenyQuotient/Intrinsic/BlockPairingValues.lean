import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.BlockPairingBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.BlockReferenceTorsion
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionPairingBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingBaseChangeFlip

/-! # Block Pairing Values -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.BlockPairingValues.Construction

noncomputable section

/-! Block-pairing pullback is the restriction of the pulled-back source
torsion pairing, with its literal values on every test scheme retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] PairingBaseChange.Construction.pulledbackGroup_commutative TorsionBaseChange.Construction.nativeTorsionPullback_commutative

variable {S S' : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (p q : A.scheme ⟶ A.scheme) [IsMonHom p] [IsMonHom q] (n : ℕ) (b : S' ⟶ S)

theorem nativeBlockBaseChangeIso_original_point (U : Over S')
    (x : U ⟶ OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)) :
    (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b (Grp.mk (OppositeKernel.Construction.torsionBlock n p)) U).symm
      (x ≫ (BlockBaseChangeGroup.Construction.nativeBlockBaseChangeIso A p n b).hom) = BlockBaseChangePoints.Construction.nativeBlockOriginalPoint A p n b U x :=
  (congrArg (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b (Grp.mk (OppositeKernel.Construction.torsionBlock n p)) U).symm
    (BlockBaseChangeGroup.Construction.nativeBlockBaseChangeIso_hom_points A p n b U x)).trans
      ((CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b (Grp.mk (OppositeKernel.Construction.torsionBlock n p)) U).symm_apply_apply _)

set_option backward.isDefEq.respectTransparency false in
theorem nativeBlockPairingPullback_value
    (e : IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock n p) (B := OppositeKernel.Construction.torsionBlock n q)
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X)) (U : Over S')
    (x : U ⟶ OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)) (y : U ⟶ OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map q)) :
    (BlockPairingBaseChange.Construction.nativeBlockPairingPullback A p q n b e).pairValue x y =
      CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange b U
        (e.pairValue (BlockBaseChangePoints.Construction.nativeBlockOriginalPoint A p n b U x) (BlockBaseChangePoints.Construction.nativeBlockOriginalPoint A q n b U y)) := by
  exact (Annihilator.Construction.SchemeBicharacter.restrict_pairValue _ _ _ x y).trans
    ((PairingBaseChangeValues.Construction.nativePairingPullback_native_value b (Grp.mk (OppositeKernel.Construction.torsionBlock n p)) (Grp.mk (OppositeKernel.Construction.torsionBlock n q)) e U
      (x ≫ (BlockBaseChangeGroup.Construction.nativeBlockBaseChangeIso A p n b).hom) (y ≫ (BlockBaseChangeGroup.Construction.nativeBlockBaseChangeIso A q n b).hom)).trans
      (congrArg (CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange b U)
        (congrArg₂ e.pairValue (nativeBlockBaseChangeIso_original_point A p n b U x)
          (nativeBlockBaseChangeIso_original_point A q n b U y))))

set_option backward.isDefEq.respectTransparency false in
theorem nativeBlockPairingPullback_source_restriction
    (e : IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) (B := Torsion.Groups.Construction.nativeTorsionScheme A.scheme n)
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X)) :
    (TorsionPairingBaseChange.Construction.nativeTorsionPairingPullback b (Grp.mk A.scheme) (Grp.mk A.scheme) n e).restrict
      (BlockGroups.Construction.fixedPointInclusion (Torsion.Groups.Construction.nativeTorsionMap n ((Over.pullback b).map p)))
      (BlockGroups.Construction.fixedPointInclusion (Torsion.Groups.Construction.nativeTorsionMap n ((Over.pullback b).map q))) =
    BlockPairingBaseChange.Construction.nativeBlockPairingPullback A p q n b
      (e.restrict (BlockGroups.Construction.fixedPointInclusion (Torsion.Groups.Construction.nativeTorsionMap n p)) (BlockGroups.Construction.fixedPointInclusion (Torsion.Groups.Construction.nativeTorsionMap n q))) := by
  apply Annihilator.Construction.SchemeBicharacter.eq_of_pairValue_eq
  intro U x y
  have hx := BlockReferenceTorsion.Construction.nativeBlockOriginalPoint_torsion A p n b U x
  have hy := BlockReferenceTorsion.Construction.nativeBlockOriginalPoint_torsion A q n b U y
  calc
    _ = CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange b U
        (e.pairValue
          (TorsionReferencePoint.Construction.nativeTorsionOriginalPoint b (Grp.mk A.scheme) n U
            (x ≫ BlockGroups.Construction.fixedPointInclusion (Torsion.Groups.Construction.nativeTorsionMap n ((Over.pullback b).map p))))
          (TorsionReferencePoint.Construction.nativeTorsionOriginalPoint b (Grp.mk A.scheme) n U
            (y ≫ BlockGroups.Construction.fixedPointInclusion (Torsion.Groups.Construction.nativeTorsionMap n ((Over.pullback b).map q))))) :=
      (Annihilator.Construction.SchemeBicharacter.restrict_pairValue _ _ _ x y).trans
        (TorsionPairingBaseChange.Construction.nativeTorsionPairingPullback_value b (Grp.mk A.scheme) (Grp.mk A.scheme) n e U _ _)
    _ = CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange b U
        ((e.restrict (BlockGroups.Construction.fixedPointInclusion (Torsion.Groups.Construction.nativeTorsionMap n p)) (BlockGroups.Construction.fixedPointInclusion (Torsion.Groups.Construction.nativeTorsionMap n q))).pairValue
          (BlockBaseChangePoints.Construction.nativeBlockOriginalPoint A p n b U x) (BlockBaseChangePoints.Construction.nativeBlockOriginalPoint A q n b U y)) :=
      congrArg (CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange b U)
        ((congrArg₂ e.pairValue hx hy).trans (Annihilator.Construction.SchemeBicharacter.restrict_pairValue _ _ _ _ _).symm)
    _ = _ := (nativeBlockPairingPullback_value A p q n b _ U x y).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.BlockPairingValues.Construction
