import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.BlockBaseChangePoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupMaps

/-! # Block Base Change Group -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.BlockBaseChangeGroup.Construction

noncomputable section

section

/-! Naturality of the native block point comparison gives the actual
scheme isomorphism between a pulled-back block and the block after base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S S' : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (p : A.scheme ⟶ A.scheme) [IsMonHom p] (n : ℕ) (b : S' ⟶ S)

set_option backward.isDefEq.respectTransparency false in
theorem nativeBlockOriginalPoint_natural {U V : Over S'} (f : U ⟶ V)
    (x : V ⟶ OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)) :
    BlockBaseChangePoints.Construction.nativeBlockOriginalPoint A p n b U (f ≫ x) =
      (Over.map b).map f ≫ BlockBaseChangePoints.Construction.nativeBlockOriginalPoint A p n b V x := by
  apply (cancel_mono (OppositeKernel.Construction.torsionBlockInclusion n p)).mp
  calc
    _ = A.baseChangePointsMulEquiv b U ((f ≫ x) ≫ OppositeKernel.Construction.torsionBlockInclusion n ((Over.pullback b).map p)) :=
      BlockBaseChangePoints.Construction.nativeBlockOriginalPoint_inclusion A p n b U (f ≫ x)
    _ = (Over.map b).map f ≫ A.baseChangePointsMulEquiv b V
        (x ≫ OppositeKernel.Construction.torsionBlockInclusion n ((Over.pullback b).map p)) := by
      apply Over.OverMorphism.ext
      change ((f.left ≫ x.left) ≫ (OppositeKernel.Construction.torsionBlockInclusion n ((Over.pullback b).map p)).left) ≫
          CategoryTheory.Limits.pullback.fst A.scheme.hom b =
        f.left ≫ ((x.left ≫ (OppositeKernel.Construction.torsionBlockInclusion n ((Over.pullback b).map p)).left) ≫
          CategoryTheory.Limits.pullback.fst A.scheme.hom b)
      simp only [Category.assoc]
    _ = _ := (congrArg ((Over.map b).map f ≫ ·)
      (BlockBaseChangePoints.Construction.nativeBlockOriginalPoint_inclusion A p n b V x).symm).trans (Category.assoc _ _ _).symm

def nativeBlockPullbackPointEquiv (U : Over S') :
    (U ⟶ OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)) ≃*
      (U ⟶ ((Over.pullback b).mapGrp.obj (Grp.mk (OppositeKernel.Construction.torsionBlock n p))).X) :=
  (BlockBaseChangePoints.Construction.nativeBlockBaseChangePointsEquiv A p n b U).trans
    (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b (Grp.mk (OppositeKernel.Construction.torsionBlock n p)) U)

set_option backward.isDefEq.respectTransparency false in
theorem nativeBlockPullbackPointEquiv_natural {U V : Over S'} (f : U ⟶ V)
    (x : V ⟶ OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)) :
    nativeBlockPullbackPointEquiv A p n b U (f ≫ x) =
      f ≫ nativeBlockPullbackPointEquiv A p n b V x := by
  apply (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b (Grp.mk (OppositeKernel.Construction.torsionBlock n p)) U).symm.injective
  change (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b (Grp.mk (OppositeKernel.Construction.torsionBlock n p)) U).symm
    (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b (Grp.mk (OppositeKernel.Construction.torsionBlock n p)) U (BlockBaseChangePoints.Construction.nativeBlockOriginalPoint A p n b U (f ≫ x))) =
    (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b (Grp.mk (OppositeKernel.Construction.torsionBlock n p)) U).symm
      (f ≫ CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b (Grp.mk (OppositeKernel.Construction.torsionBlock n p)) V (BlockBaseChangePoints.Construction.nativeBlockOriginalPoint A p n b V x))
  exact ((CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b (Grp.mk (OppositeKernel.Construction.torsionBlock n p)) U).symm_apply_apply _).trans
    ((nativeBlockOriginalPoint_natural A p n b f x).trans
      ((congrArg ((Over.map b).map f ≫ ·)
        ((CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b (Grp.mk (OppositeKernel.Construction.torsionBlock n p)) V).symm_apply_apply _).symm).trans
          (Relative.ParameterBaseChange.Construction.pullbackPointMulEquiv_symm_natural b (Grp.mk (OppositeKernel.Construction.torsionBlock n p)) f
            (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b (Grp.mk (OppositeKernel.Construction.torsionBlock n p)) V
              (BlockBaseChangePoints.Construction.nativeBlockOriginalPoint A p n b V x))).symm))

def nativeBlockBaseChangeIso :
    OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p) ≅ (Over.pullback b).obj (OppositeKernel.Construction.torsionBlock n p) :=
  Yoneda.ext _ _
    (fun {U} x => nativeBlockPullbackPointEquiv A p n b U x)
    (fun {U} x => (nativeBlockPullbackPointEquiv A p n b U).symm x)
    (fun {U} x => (nativeBlockPullbackPointEquiv A p n b U).symm_apply_apply x)
    (fun {U} x => (nativeBlockPullbackPointEquiv A p n b U).apply_symm_apply x)
    (fun f x => nativeBlockPullbackPointEquiv_natural A p n b f x)

theorem nativeBlockBaseChangeIso_hom_points (U : Over S')
    (x : U ⟶ OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)) :
    x ≫ (nativeBlockBaseChangeIso A p n b).hom = nativeBlockPullbackPointEquiv A p n b U x := by
  change x ≫ nativeBlockPullbackPointEquiv A p n b _ (𝟙 _) = _
  exact (nativeBlockPullbackPointEquiv_natural A p n b x (𝟙 _)).symm.trans
    (congrArg (nativeBlockPullbackPointEquiv A p n b U) (Category.comp_id x))

end

/-! The actual native torsion-block base-change isomorphism preserves
the group law and its inclusion in the pulled-back abelian scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S S' : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (p : A.scheme ⟶ A.scheme) [IsMonHom p] (n : ℕ) (b : S' ⟶ S)

instance nativeBlockBaseChangeIso_hom_isMonHom : IsMonHom (nativeBlockBaseChangeIso A p n b).hom := by
  apply GroupMaps.Construction.isMonHom_of_pointwise
  · intro U
    rw [nativeBlockBaseChangeIso_hom_points]
    exact (nativeBlockPullbackPointEquiv A p n b U).map_one
  · intro U x y
    rw [nativeBlockBaseChangeIso_hom_points, nativeBlockBaseChangeIso_hom_points,
      nativeBlockBaseChangeIso_hom_points]
    exact (nativeBlockPullbackPointEquiv A p n b U).map_mul x y

def nativeBlockBaseChangeGrpIso :
    Grp.mk (OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)) ≅
      (Over.pullback b).mapGrp.obj (Grp.mk (OppositeKernel.Construction.torsionBlock n p)) :=
  Grp.mkIso' (nativeBlockBaseChangeIso A p n b)

set_option backward.isDefEq.respectTransparency false in
theorem nativeBlockBaseChangeIso_hom_inclusion :
    (nativeBlockBaseChangeIso A p n b).hom ≫ (Over.pullback b).map (OppositeKernel.Construction.torsionBlockInclusion n p) =
      OppositeKernel.Construction.torsionBlockInclusion n ((Over.pullback b).map p) := by
  let U := OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)
  let H := Grp.mk (OppositeKernel.Construction.torsionBlock n p)
  let J := Grp.mk A.scheme
  let i : H ⟶ J := Grp.homMk (OppositeKernel.Construction.torsionBlockInclusion n p)
  have hh : (nativeBlockBaseChangeIso A p n b).hom = nativeBlockPullbackPointEquiv A p n b U (𝟙 U) :=
    (Category.id_comp _).symm.trans (nativeBlockBaseChangeIso_hom_points A p n b U (𝟙 U))
  apply (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b J U).symm.injective
  calc
    _ = (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b H U).symm (nativeBlockBaseChangeIso A p n b).hom ≫ OppositeKernel.Construction.torsionBlockInclusion n p :=
      CartierDuality.EvaluationBaseChange.Construction.Schemes.pullbackPointMulEquiv_symm_comp b i U (nativeBlockBaseChangeIso A p n b).hom
    _ = BlockBaseChangePoints.Construction.nativeBlockOriginalPoint A p n b U (𝟙 U) ≫ OppositeKernel.Construction.torsionBlockInclusion n p :=
      congrArg (· ≫ OppositeKernel.Construction.torsionBlockInclusion n p)
        ((congrArg (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b H U).symm hh).trans
          ((CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b H U).symm_apply_apply _))
    _ = _ := (BlockBaseChangePoints.Construction.nativeBlockOriginalPoint_inclusion A p n b U (𝟙 U)).trans
      (congrArg (A.baseChangePointsMulEquiv b U) (Category.id_comp _))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.BlockBaseChangeGroup.Construction
