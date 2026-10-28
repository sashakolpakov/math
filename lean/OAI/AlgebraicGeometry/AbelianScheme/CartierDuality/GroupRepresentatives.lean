import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterGroupSheaf
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RepresentabilityDescent

/-! # Group Representatives -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GroupRepresentatives

noncomputable section

/-!
# CartierDuality: native commutative group representatives of character sheaves
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.Schemes

/-- A finite locally free commutative group scheme representing the
actual character functor, with an isomorphism retaining the group laws. -/
structure CharacterGroupRepresentation (S : Scheme.{u}) (G : Grp (Over S)) where
  dual : Grp (Over S)
  commutative : IsCommMonObj dual.X
  finite : IsFinite dual.X.hom
  flat : Flat dual.X.hom
  finitelyPresented : LocallyOfFinitePresentation dual.X.hom
  pointsIso : yonedaGrp.obj dual ≅
    CharacterGroupSheaf.Construction.Schemes.nativeCharacterCommGroupPresheaf S G ⋙ forget₂ CommGrpCat GrpCat

/-- A scheme representing characters inherits their pointwise
commutative group structure. The original geometric representative is
retained, so finiteness and local freeness are unchanged. -/
def characterGroupRepresentationOfRepresentable (S : Scheme.{u}) (G : Grp (Over S))
    (h : CharacterFunctor.Construction.Schemes.FiniteLocallyFreeRepresentable (CharacterSheaf.Construction.Schemes.characterSheaf S G)) :
    CharacterGroupRepresentation S G := by
  let X := Classical.choose h
  have hX := Classical.choose_spec h
  let e := Classical.choice hX.2.2.2
  let rBig := (Functor.RepresentableBy.equivUliftYonedaIso
    (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj X).symm ((sheafToPresheaf _ _).mapIso e)
  let rSmall : (SmallCharacters.Construction.Schemes.nativeCharacterPresheaf S G).RepresentableBy X :=
    Functor.representableByUliftFunctorEquiv
      (rBig.ofIso (SmallCharacters.Construction.Schemes.nativeCharacterPresheafIso S G).symm)
  let F := CharacterGroupSheaf.Construction.Schemes.nativeCharacterCommGroupPresheaf S G
  let : CommGrpObj X := CommGrpObj.ofRepresentableBy X F rSmall
  refine
    { dual := Grp.mk X
      commutative := inferInstance
      finite := hX.1
      flat := hX.2.1
      finitelyPresented := hX.2.2.1
      pointsIso := ?_ }
  exact yonedaGrpObjIsoOfRepresentableBy X (F ⋙ forget₂ CommGrpCat GrpCat) rSmall

/-- Forgetting the group structure of a character representative
recovers a representation of the native character presheaf. -/
def CharacterGroupRepresentation.nativeRepresentableBy {S : Scheme.{u}}
    {G : Grp (Over S)} (D : CharacterGroupRepresentation S G) :
    (SmallCharacters.Construction.Schemes.nativeCharacterPresheaf S G).RepresentableBy D.dual.X :=
  Functor.representableByEquiv.symm
    (Functor.isoWhiskerRight D.pointsIso (forget GrpCat))

/-- The group representative also represents the original big-site
character sheaf, with its actual restriction maps. -/
def CharacterGroupRepresentation.sheafIso {S : Scheme.{u}}
    {G : Grp (Over S)} (D : CharacterGroupRepresentation S G) :
    CharacterFunctor.Construction.Schemes.pointSheaf S D.dual.X ≅ CharacterSheaf.Construction.Schemes.characterSheaf S G :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    ((Functor.RepresentableBy.equivUliftYonedaIso (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj D.dual.X)
      ((Functor.representableByUliftFunctorEquiv.symm D.nativeRepresentableBy).ofIso
        (SmallCharacters.Construction.Schemes.nativeCharacterPresheafIso S G)))

end Construction.Schemes

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GroupRepresentatives
