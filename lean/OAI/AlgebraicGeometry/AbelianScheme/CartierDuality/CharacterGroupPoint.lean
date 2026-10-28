import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GroupMap

/-! # Character Group Point -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterGroupPoint

noncomputable section

/-!
# CartierDuality: group-valued isomorphisms from character representations
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u v w

namespace Construction

namespace CharacterGroupIsos

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- A multiplicative isomorphism of the underlying represented
presheaves gives group isomorphisms on every test object. -/
def pointMulEquiv (F : Cᵒᵖ ⥤ CommGrpCat.{max v w}) (D : Grp C)
    (e : uliftYoneda.{w}.obj D.X ≅ F ⋙ forget CommGrpCat)
    (he : ∀ (T : C) (f g : T ⟶ D.X),
      e.hom.app (Opposite.op T) (ULift.up (f * g)) =
        e.hom.app (Opposite.op T) (ULift.up f) * e.hom.app (Opposite.op T) (ULift.up g))
    (T : C) : (T ⟶ D.X) ≃* F.obj (Opposite.op T) where
  toEquiv := Equiv.ulift.symm.trans (e.app (Opposite.op T)).toEquiv
  map_mul' := he T

/-- The point-group equivalence is the specified underlying presheaf map. -/
theorem pointMulEquiv_apply (F : Cᵒᵖ ⥤ CommGrpCat.{max v w}) (D : Grp C)
    (e : uliftYoneda.{w}.obj D.X ≅ F ⋙ forget CommGrpCat)
    (he : ∀ (T : C) (f g : T ⟶ D.X),
      e.hom.app (Opposite.op T) (ULift.up (f * g)) =
        e.hom.app (Opposite.op T) (ULift.up f) * e.hom.app (Opposite.op T) (ULift.up g))
    (T : C) (f : T ⟶ D.X) :
    pointMulEquiv F D e he T f = e.hom.app (Opposite.op T) (ULift.up f) := rfl

/-- The point-group equivalences commute with all restrictions. -/
theorem pointMulEquiv_natural (F : Cᵒᵖ ⥤ CommGrpCat.{max v w}) (D : Grp C)
    (e : uliftYoneda.{w}.obj D.X ≅ F ⋙ forget CommGrpCat)
    (he : ∀ (T : C) (f g : T ⟶ D.X),
      e.hom.app (Opposite.op T) (ULift.up (f * g)) =
        e.hom.app (Opposite.op T) (ULift.up f) * e.hom.app (Opposite.op T) (ULift.up g))
    {T U : C} (f : U ⟶ T) (x : T ⟶ D.X) :
    pointMulEquiv F D e he U (f ≫ x) = F.map f.op (pointMulEquiv F D e he T x) :=
  GroupMap.Construction.GroupMapDescent.pointMap_naturality (F ⋙ forget CommGrpCat) D.X e.hom f.op x

end CharacterGroupIsos

namespace Schemes

/-- A multiplicative character-sheaf representation is an isomorphism
of the actual group-valued functors of points. -/
def characterGroupPointIso (S : Scheme.{u}) (G D : Grp (Over S))
    (e : CharacterFunctor.Construction.Schemes.pointSheaf S D.X ≅ CharacterSheaf.Construction.Schemes.characterSheaf S G)
    (he : ∀ (T : Over S) (f g : T ⟶ D.X),
      e.hom.hom.app (Opposite.op T) (ULift.up (f * g)) =
        e.hom.hom.app (Opposite.op T) (ULift.up f) *
          e.hom.hom.app (Opposite.op T) (ULift.up g)) :
    yonedaGrp.obj D ≅ CharacterGroupSheaf.Construction.Schemes.nativeCharacterCommGroupPresheaf S G ⋙ forget₂ CommGrpCat GrpCat := by
  let F := CharacterGroupSheaf.Construction.Schemes.characterCommGroupPresheaf S G
  let i : uliftYoneda.{u + 1}.obj D.X ≅ F ⋙ forget CommGrpCat :=
    (sheafToPresheaf _ _).mapIso e
  let p := CharacterGroupIsos.pointMulEquiv F D i he
  refine NatIso.ofComponents (fun T =>
    ((p T.unop).trans (CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv S G T).symm).toGrpIso) ?_
  intro T U f
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  apply (CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv S G U).injective
  change CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv S G U
      ((CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv S G U).symm (p U.unop (f.unop ≫ x))) =
    CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv S G U
      ((CharacterGroupSheaf.Construction.Schemes.nativeCharacterCommGroupPresheaf S G).map f
        ((CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv S G T).symm (p T.unop x)))
  have hp := CharacterGroupIsos.pointMulEquiv_natural F D i he f.unop x
  have hs := CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv_natural S G f
    ((CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv S G T).symm (p T.unop x))
  have hs' := hs.trans (congrArg ((CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.map f)
    ((CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv S G T).apply_symm_apply (p T.unop x)))
  exact ((CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv S G U).apply_symm_apply _).trans (hp.trans hs'.symm)

/-- The group-valued refinement has exactly the original character
section as its value after the size comparison. -/
theorem characterGroupPointIso_character (S : Scheme.{u}) (G D : Grp (Over S))
    (e : CharacterFunctor.Construction.Schemes.pointSheaf S D.X ≅ CharacterSheaf.Construction.Schemes.characterSheaf S G)
    (he : ∀ (T : Over S) (f g : T ⟶ D.X),
      e.hom.hom.app (Opposite.op T) (ULift.up (f * g)) =
        e.hom.hom.app (Opposite.op T) (ULift.up f) *
          e.hom.hom.app (Opposite.op T) (ULift.up g))
    (T : Over S) (f : T ⟶ D.X) :
    CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv S G (Opposite.op T)
      ((characterGroupPointIso S G D e he).hom.app (Opposite.op T) f) =
        e.hom.hom.app (Opposite.op T) (ULift.up f) := by
  change CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv S G (Opposite.op T)
    ((CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv S G (Opposite.op T)).symm
      (e.hom.hom.app (Opposite.op T) (ULift.up f))) = _
  exact (CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv S G (Opposite.op T)).apply_symm_apply _

end Schemes

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterGroupPoint
