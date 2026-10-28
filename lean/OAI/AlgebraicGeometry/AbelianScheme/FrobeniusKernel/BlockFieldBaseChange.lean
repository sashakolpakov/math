import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BlockBaseChangePoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FieldBaseChangePoints

/-! # Block Field Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BlockFieldBaseChange.Construction

noncomputable section

/-! Scalar extension of the exact affine CMPoints character-block functor.
The comparison retains its inclusion in the original abelian point group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

variable {k k' : Type} [Field k] [Field k'] [Algebra k k']
variable {O : Type} [CommRing O] {g q : ℕ} [Fact q.Prime]
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A)
variable (χ : O →+* PadicInt q) (n : ℕ)

def l45AffineBlockFieldBaseChangeIso :
    PELModuli.CMPoints.BlocksProjectors.affineBlockFunctor
      (A.pullback (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k')))
      (ρ.pullback (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k'))) χ n ≅
        AffineFieldRestriction.Construction.restrictFieldAlgebras (k := k) (k' := k') ⋙ PELModuli.CMPoints.BlocksProjectors.affineBlockFunctor A ρ χ n :=
  Functor.isoWhiskerLeft (algSpec (.of k')).rightOp
      (BlockBaseChangePoints.Construction.l45BlockFunctorBaseChangeIso A ρ (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k')) χ n) ≪≫
    (Functor.isoWhiskerRight (FieldBaseChangePoints.Construction.affineFieldRestrictionPointIso (k := k) (k' := k'))
      (PELModuli.CMPoints.BlocksProjectors.blockFunctor A ρ χ n)).symm

theorem l45AffineBlockFieldBaseChangeIso_value (R : CommAlgCat k')
    (x : PELModuli.CMPoints.BlocksProjectors.blockPoints
      (A.pullback (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k')))
      (ρ.pullback (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k'))) χ n
      (GroupSchemes.FiniteEtale.affine k' R)) :
    ((l45AffineBlockFieldBaseChangeIso (k' := k') A ρ χ n).hom.app R x).val =
      (AffineFieldRestriction.Construction.restrictedAffineBaseIso (k := k) R).inv ≫
        A.baseChangePointsMulEquiv (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k'))
          (GroupSchemes.FiniteEtale.affine k' R) x.val := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BlockFieldBaseChange.Construction
