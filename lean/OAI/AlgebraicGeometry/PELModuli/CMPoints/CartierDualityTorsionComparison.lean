import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors
import OAI.AlgebraicGeometry.PELModuli.CMPoints.BaseCharacters
import OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion

/-! # Cartier Duality Torsion Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.CartierDualityTorsionComparison

noncomputable section

/-! The native CartierDuality torsion kernel and the CMPoints torsion-point functor
describe the same group on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (n : ℕ)

def nativeTorsionPointsMulEquiv (T : Over S) :
    (T ⟶ (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup (Grp.mk A.scheme) n).X) ≃* A.torsionPoints n T where
  toEquiv := BlocksProjectors.torsionPointsEquiv A n T
  map_mul' x y := by
    apply Subtype.ext
    exact MonObj.mul_comp x y (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionInclusion (Grp.mk A.scheme) n).hom.hom

def nativeTorsionPointsIso :
    yonedaGrp.obj (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup (Grp.mk A.scheme) n) ≅ A.torsionFunctor n :=
  NatIso.ofComponents (fun T => (nativeTorsionPointsMulEquiv A n T.unop).toGrpIso) (by
    intro T U f
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact Subtype.ext (Category.assoc f.unop x (BlocksProjectors.torsionInclusion A n)))

def torsionPointGroups : (Over S)ᵒᵖ ⥤ CommGrpCat where
  obj T := CommGrpCat.of (A.torsionPoints n T.unop)
  map f := CommGrpCat.ofHom ((A.torsionFunctor n).map f).hom
  map_id T := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    exact (A.torsionFunctor n).map_id_apply T
  map_comp f h := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    exact (A.torsionFunctor n).map_comp_apply f h

def nativeTorsionCommPointsIso :
    AbelianScheme.CartierDuality.CharacterGroupSheaf.Construction.Schemes.commGroupPoints S (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup (Grp.mk A.scheme) n) ≅ torsionPointGroups A n :=
  NatIso.ofComponents (fun T => (nativeTorsionPointsMulEquiv A n T.unop).toCommGrpIso) (by
    intro T U f
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact Subtype.ext (Category.assoc f.unop x (BlocksProjectors.torsionInclusion A n)))

def torsionSheafPointIso :
    (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A.scheme)) n).obj ≅
      torsionPointGroups A n ⋙ CommGrpCat.uliftFunctor.{1, 0} :=
  (sheafToPresheaf (Scheme.fppfTopology.over S) CommGrpCat.{1}).mapIso
      (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk A.scheme) n).symm ≪≫
    Functor.isoWhiskerRight (nativeTorsionCommPointsIso A n) CommGrpCat.uliftFunctor.{1, 0}

universe v

def characterGroupCongr {F G : (Over S)ᵒᵖ ⥤ GrpCat.{v}}
    (e : F ≅ G) (K : (Over S)ᵒᵖ ⥤ CommGrpCat.{v}) :
    AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.CommutativeSheaves.internalHom F K ≅
      AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.CommutativeSheaves.internalHom G K where
  hom := AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.CommutativeSheaves.restriction e.inv K
  inv := AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.CommutativeSheaves.restriction e.hom K
  hom_inv_id := by
    rw [← AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.CommutativeSheaves.restriction_comp,
      e.hom_inv_id, AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.CommutativeSheaves.restriction_id]
  inv_hom_id := by
    rw [← AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.CommutativeSheaves.restriction_comp,
      e.inv_hom_id, AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.CommutativeSheaves.restriction_id]

def torsionCartierPointIso :
    (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A.scheme)) n)).obj ≅
      AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.CommutativeSheaves.internalHom (A.torsionFunctor n)
        (AbelianScheme.CartierDuality.CharacterGroupSheaf.Construction.Schemes.commGroupPoints S (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S)) :=
  characterGroupCongr
      (Functor.isoWhiskerRight (torsionSheafPointIso A n) (forget₂ CommGrpCat GrpCat))
      (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.multiplicativeFppfAb S).obj ≪≫
    (AbelianScheme.CartierDuality.SheafCharacterComparison.Construction.CommutativeSheaves.uliftInternalHomIso (A.torsionFunctor n)
      (AbelianScheme.CartierDuality.CharacterGroupSheaf.Construction.Schemes.commGroupPoints S (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S))).symm

def torsionCartierCharacterIso :
    (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A.scheme)) n)).obj ⋙
        forget CommGrpCat ≅ DualityPairing.cartierCharacters (A.torsionFunctor n) :=
  Functor.isoWhiskerRight (torsionCartierPointIso A n) (forget CommGrpCat)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.CartierDualityTorsionComparison
