import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.AffineFieldRestriction
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GroupFieldPointTransport
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterBaseChange

/-! # Field Base Change Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FieldBaseChangePoints.Construction

noncomputable section

/-! The scalar-extended finite group has the original group of points
on each scalar-restricted affine test algebra. This comparison is a
natural group isomorphism, preserving all infinitesimal tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

universe u

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']

def affineFieldRestrictionPointIso :
    AffineFieldRestriction.Construction.restrictFieldAlgebras (k := k) (k' := k') ⋙ (algSpec (.of k)).rightOp ≅
      (algSpec (.of k')).rightOp ⋙ (Over.map (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k'))).op :=
  NatIso.ofComponents (fun R => (AffineFieldRestriction.Construction.restrictedAffineBaseIso (k := k) R).op) (by
    intro R S a
    apply Quiver.Hom.unop_inj
    exact (AffineFieldRestriction.Construction.restrictedAffineBaseIso_naturality (k := k) a).symm)

variable (G : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k)

def finiteGroupFieldBaseChangePointsIso :
    (GroupFieldBaseChange.Construction.finiteGroupFieldBaseChange (k' := k') G).points ⋙ forget₂ CommGrpCat GrpCat ≅
      AffineFieldRestriction.Construction.restrictFieldAlgebras (k := k) (k' := k') ⋙ G.points ⋙ forget₂ CommGrpCat GrpCat :=
  Functor.isoWhiskerLeft (algSpec (.of k')).rightOp
      (yonedaGrp.mapIso (GroupFieldBaseChange.Construction.finiteGroupFieldBaseChangeGroupIso (k' := k') G)).symm ≪≫
    Functor.isoWhiskerLeft (algSpec (.of k')).rightOp
      (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackGroupPointIso (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k'))
        (Grp.mk G.scheme)).symm ≪≫
      (Functor.isoWhiskerRight (affineFieldRestrictionPointIso (k := k) (k' := k'))
        (yonedaGrp.obj (Grp.mk G.scheme))).symm

theorem finiteGroupFieldBaseChangePointsIso_apply (R : CommAlgCat.{u} k')
    (x : GroupSchemes.FiniteEtale.affine k' R ⟶ (GroupFieldBaseChange.Construction.finiteGroupFieldBaseChange (k' := k') G).scheme) :
    (finiteGroupFieldBaseChangePointsIso (k' := k') G).hom.app R x =
      (AffineFieldRestriction.Construction.restrictedAffineBaseIso (k := k) R).inv ≫
        (GroupFieldPointTransport.Construction.finiteGroupFieldPointEquiv G (GroupSchemes.FiniteEtale.affine k' R)).symm x := rfl

variable {G} {H : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k} (a : G.scheme ⟶ H.scheme)

theorem finiteGroupFieldBaseChangePointsIso_postcomp (R : CommAlgCat.{u} k')
    (x : GroupSchemes.FiniteEtale.affine k' R ⟶ (GroupFieldBaseChange.Construction.finiteGroupFieldBaseChange (k' := k') G).scheme) :
    (finiteGroupFieldBaseChangePointsIso (k' := k') H).hom.app R
        (x ≫ FieldBaseChangeMaps.Construction.finiteGroupFieldBaseChangeSchemeMap (k' := k') a) =
      (finiteGroupFieldBaseChangePointsIso (k' := k') G).hom.app R x ≫ a := by
  rw [finiteGroupFieldBaseChangePointsIso_apply, finiteGroupFieldBaseChangePointsIso_apply,
    GroupFieldPointTransport.Construction.finiteGroupFieldPointEquiv_symm_postcomp]
  exact (Category.assoc (AffineFieldRestriction.Construction.restrictedAffineBaseIso (k := k) R).inv
    ((GroupFieldPointTransport.Construction.finiteGroupFieldPointEquiv G (GroupSchemes.FiniteEtale.affine k' R)).symm x) a).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FieldBaseChangePoints.Construction
