import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterGroupOf
import Mathlib.Algebra.Category.Grp.Ulift

/-! # Commutative Sheaves Ab -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CommutativeSheavesAb

noncomputable section

/-!
# CartierDuality: actual commutative fppf sheaves and their character sheaves
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u v w

namespace Construction

namespace CommutativeSheaves

variable {C : Type u} [Category.{v} C]

/-- The internal group Hom into a commutative-group presheaf, with
pointwise multiplication and the actual restriction maps. -/
def internalHom (F : Cᵒᵖ ⥤ GrpCat.{w}) (K : Cᵒᵖ ⥤ CommGrpCat.{w}) :
    Cᵒᵖ ⥤ CommGrpCat.{max u v w} where
  obj T := CommGrpCat.of ((presheafHom F (K ⋙ forget₂ CommGrpCat GrpCat)).obj T)
  map f := CommGrpCat.ofHom
    { toFun := (presheafHom F (K ⋙ forget₂ CommGrpCat GrpCat)).map f
      map_one' := rfl
      map_mul' _ _ := rfl }
  map_id T := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro χ
    exact (presheafHom F (K ⋙ forget₂ CommGrpCat GrpCat)).map_id_apply T χ
  map_comp f g := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro χ
    exact (presheafHom F (K ⋙ forget₂ CommGrpCat GrpCat)).map_comp_apply f g χ

/-- Internal group Hom is a sheaf whenever its target is a sheaf. -/
def internalHomSheaf (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ GrpCat.{w})
    (K : Sheaf J CommGrpCat.{w}) : Sheaf J CommGrpCat.{max u v w} :=
  ⟨internalHom F K.obj,
    Presheaf.isSheaf_of_isSheaf_comp J (internalHom F K.obj) (forget CommGrpCat)
      (Presheaf.IsSheaf.hom (F := F) (G := K.obj ⋙ forget₂ CommGrpCat GrpCat)
        ((sheafCompose J (forget₂ CommGrpCat GrpCat)).obj K).property)⟩

/-- Restriction in the source is a morphism of the actual internal-Hom
commutative-group presheaves. -/
def restriction {F H : Cᵒᵖ ⥤ GrpCat.{w}} (a : H ⟶ F) (K : Cᵒᵖ ⥤ CommGrpCat.{w}) :
    internalHom F K ⟶ internalHom H K where
  app T := CommGrpCat.ofHom
    { toFun := fun χ => Functor.whiskerLeft (Over.forget T.unop).op a ≫ χ
      map_one' := rfl
      map_mul' _ _ := rfl }
  naturality := by
    intro T U f
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro χ
    apply NatTrans.ext
    rfl

/-- Character restriction along an identity is the identity. -/
theorem restriction_id (F : Cᵒᵖ ⥤ GrpCat.{w}) (K : Cᵒᵖ ⥤ CommGrpCat.{w}) :
    restriction (𝟙 F) K = 𝟙 (internalHom F K) := by
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  intro χ
  exact Category.id_comp χ

/-- Character restriction reverses composition. -/
theorem restriction_comp {F H L : Cᵒᵖ ⥤ GrpCat.{w}} (a : H ⟶ F) (b : L ⟶ H)
    (K : Cᵒᵖ ⥤ CommGrpCat.{w}) :
    restriction (b ≫ a) K = restriction a K ≫ restriction b K := by
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  intro χ
  exact Category.assoc (Functor.whiskerLeft (Over.forget T.unop).op b)
    (Functor.whiskerLeft (Over.forget T.unop).op a) χ

end CommutativeSheaves

namespace Schemes

/-- Commutative group sheaves on the big fppf site. The value universe
also contains the natural transformations defining their character sheaves. -/
abbrev FppfAb (S : Scheme.{u}) := Sheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1}

/-- Small commutative-group-valued scheme points satisfy fppf descent. -/
def commGroupPointSheaf (S : Scheme.{u}) (G : Grp (Over S)) [IsCommMonObj G.X] :
    Sheaf (Scheme.fppfTopology.over S) CommGrpCat.{u} :=
  ⟨CharacterGroupSheaf.Construction.Schemes.commGroupPoints S G,
    Presheaf.isSheaf_of_isSheaf_comp (Scheme.fppfTopology.over S) (CharacterGroupSheaf.Construction.Schemes.commGroupPoints S G)
      (forget₂ CommGrpCat GrpCat) (CharacterSheaf.Construction.Schemes.groupPoints_isSheaf S G)⟩

/-- The actual represented commutative fppf sheaf in the common value universe. -/
def representedFppfAb (S : Scheme.{u}) (G : Grp (Over S)) [IsCommMonObj G.X] : FppfAb S :=
  (sheafCompose (Scheme.fppfTopology.over S) CommGrpCat.uliftFunctor.{u + 1, u}).obj
    (commGroupPointSheaf S G)

/-- The multiplicative-group sheaf on the big fppf site. -/
def multiplicativeFppfAb (S : Scheme.{u}) : FppfAb S :=
  representedFppfAb S (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S)

/-- The Cartier character sheaf of an arbitrary commutative fppf
sheaf. Its definition assumes no representability or duality theorem. -/
def cartierDualSheaf {S : Scheme.{u}} (G : FppfAb S) : FppfAb S :=
  CommutativeSheaves.internalHomSheaf (Scheme.fppfTopology.over S)
    (G.obj ⋙ forget₂ CommGrpCat GrpCat) (multiplicativeFppfAb S)

/-- The character construction is contravariant on all commutative
fppf sheaves, independently of finite locally free representability. -/
def cartierDualSheafFunctor (S : Scheme.{u}) : (FppfAb S)ᵒᵖ ⥤ FppfAb S where
  obj G := cartierDualSheaf G.unop
  map a := ⟨CommutativeSheaves.restriction
    (Functor.whiskerRight a.unop.hom (forget₂ CommGrpCat GrpCat)) (multiplicativeFppfAb S).obj⟩
  map_id G := by
    apply (sheafToPresheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1}).map_injective
    exact CommutativeSheaves.restriction_id (G.unop.obj ⋙ forget₂ CommGrpCat GrpCat)
      (multiplicativeFppfAb S).obj
  map_comp a b := by
    apply (sheafToPresheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1}).map_injective
    exact CommutativeSheaves.restriction_comp
      (Functor.whiskerRight a.unop.hom (forget₂ CommGrpCat GrpCat))
      (Functor.whiskerRight b.unop.hom (forget₂ CommGrpCat GrpCat)) (multiplicativeFppfAb S).obj

end Schemes

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CommutativeSheavesAb
