import OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemePullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Algebra.Group.TransferInstance

/-! # Group Sheafification -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupSheafification

noncomputable section

/-! The group structure on the underlying type-valued fppf sheafification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {S : Scheme.{u}}

instance picardSheafificationCommGroupColimits :
    CategoryTheory.Limits.HasColimitsOfSize.{u + 1, u + 1} CommGrpCat.{u + 1} :=
  Adjunction.has_colimits_of_equivalence commGroupAddCommGroupEquivalence.functor

def picardTypeSheafifyEquiv (P : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1}) (T : (Over S)ᵒᵖ) :
    (sheafify (Scheme.fppfTopology.over S) (P ⋙ forget CommGrpCat)).obj T ≃
      (sheafify (Scheme.fppfTopology.over S) P).obj T :=
  ((sheafifyComposeIso (Scheme.fppfTopology.over S) (forget CommGrpCat) P).app T).toEquiv

instance picardTypeSheafifyCommGroup (P : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1}) (T : (Over S)ᵒᵖ) :
    CommGroup ((sheafify (Scheme.fppfTopology.over S) (P ⋙ forget CommGrpCat)).obj T) :=
  (picardTypeSheafifyEquiv P T).commGroup

def picardTypeSheafifyMulEquiv (P : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1}) (T : (Over S)ᵒᵖ) :
    (sheafify (Scheme.fppfTopology.over S) (P ⋙ forget CommGrpCat)).obj T ≃*
      (sheafify (Scheme.fppfTopology.over S) P).obj T :=
  (picardTypeSheafifyEquiv P T).mulEquiv

theorem picardTypeSheafifyEquiv_unit (P : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1})
    (T : (Over S)ᵒᵖ) (x : P.obj T) :
    picardTypeSheafifyEquiv P T ((toSheafify (Scheme.fppfTopology.over S)
      (P ⋙ forget CommGrpCat)).app T x) =
      (toSheafify (Scheme.fppfTopology.over S) P).app T x := by
  have h := congrArg (fun a => a.app T) (sheafComposeIso_hom_fac
    (Scheme.fppfTopology.over S) (forget CommGrpCat) P)
  exact ConcreteCategory.congr_hom h x

def picardTypeSheafifyUnitHom (P : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1}) (T : (Over S)ᵒᵖ) :
    P.obj T →* (sheafify (Scheme.fppfTopology.over S) (P ⋙ forget CommGrpCat)).obj T where
  toFun := (toSheafify (Scheme.fppfTopology.over S) (P ⋙ forget CommGrpCat)).app T
  map_one' := by
    apply (picardTypeSheafifyEquiv P T).injective
    rw [picardTypeSheafifyEquiv_unit]
    exact ((toSheafify (Scheme.fppfTopology.over S) P).app T).hom.map_one.trans
      (picardTypeSheafifyMulEquiv P T).map_one.symm
  map_mul' a b := by
    apply (picardTypeSheafifyEquiv P T).injective
    rw [picardTypeSheafifyEquiv_unit]
    change _ = picardTypeSheafifyMulEquiv P T (_ * _)
    rw [(picardTypeSheafifyMulEquiv P T).map_mul]
    change _ = picardTypeSheafifyEquiv P T (_ ) * picardTypeSheafifyEquiv P T (_)
    rw [picardTypeSheafifyEquiv_unit, picardTypeSheafifyEquiv_unit]
    exact ((toSheafify (Scheme.fppfTopology.over S) P).app T).hom.map_mul a b

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupSheafification
