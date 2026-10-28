import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CommutativeSheavesAb

/-! # Sheaf Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafBaseChange

noncomputable section

/-!
# CartierDuality: base change of commutative fppf sheaves and their actual characters
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u v w

namespace Construction

namespace CommutativeSheaves

variable {C : Type u} [Category.{v} C] {C' : Type u} [Category.{v} C']

/-- Restriction to a functor inducing equivalences on all slices
preserves the actual internal Hom as a commutative-group presheaf. -/
def internalHomWhiskerIso (H : C' ⥤ C) (F : Cᵒᵖ ⥤ GrpCat.{w}) (K : Cᵒᵖ ⥤ CommGrpCat.{w})
    [∀ X : C', (Over.post (X := X) H).IsEquivalence] :
    H.op ⋙ CommutativeSheavesAb.Construction.CommutativeSheaves.internalHom F K ≅ CommutativeSheavesAb.Construction.CommutativeSheaves.internalHom (H.op ⋙ F) (H.op ⋙ K) := by
  let c := CharacterBaseChange.Construction.Slices.presheafHomWhiskerMap H F (K ⋙ forget₂ CommGrpCat GrpCat)
  let hc : IsIso c := CharacterBaseChange.Construction.Slices.presheafHomWhiskerMap_isIso H F (K ⋙ forget₂ CommGrpCat GrpCat)
  exact CharacterGroupOf.Construction.CharacterGroupBaseChange.commGroupIsoOfTypeIso (@asIso _ _ _ _ c hc)
    (CharacterGroupOf.Construction.CharacterGroupBaseChange.whiskerMap_mul H F K)

/-- Natural isomorphisms of source and target give the expected
isomorphism of actual commutative character groups. -/
def internalHomCongr {F F' : Cᵒᵖ ⥤ GrpCat.{w}} {K K' : Cᵒᵖ ⥤ CommGrpCat.{w}}
    (a : F ≅ F') (b : K ≅ K') : CommutativeSheavesAb.Construction.CommutativeSheaves.internalHom F K ≅ CommutativeSheavesAb.Construction.CommutativeSheaves.internalHom F' K' :=
  CharacterGroupOf.Construction.CharacterGroupBaseChange.commGroupIsoOfTypeIso
    (CharacterBaseChange.Construction.Slices.presheafHomCongr a (Functor.isoWhiskerRight b (forget₂ CommGrpCat GrpCat)))
    (CharacterGroupOf.Construction.CharacterGroupBaseChange.congr_mul a (Functor.isoWhiskerRight b (forget₂ CommGrpCat GrpCat)))

end CommutativeSheaves

namespace Schemes

/-- Scheme-theoretic base change on the big fppf category of
commutative-group sheaves. -/
abbrev baseChangeFppfAb {S T : Scheme.{u}} (f : T ⟶ S) : CommutativeSheavesAb.Construction.Schemes.FppfAb S ⥤ CommutativeSheavesAb.Construction.Schemes.FppfAb T :=
  Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} f

/-- Native group isomorphisms induce the corresponding isomorphisms
of commutative fppf sheaves in the common universe. -/
def representedFppfAbIso {S : Scheme.{u}} {G H : Grp (Over S)}
    [IsCommMonObj G.X] [IsCommMonObj H.X] (e : G ≅ H) :
    CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G ≅ CommutativeSheavesAb.Construction.Schemes.representedFppfAb S H :=
  (sheafCompose (Scheme.fppfTopology.over S) CommGrpCat.uliftFunctor.{u + 1, u}).mapIso
    ((fullyFaithfulSheafToPresheaf _ _).preimageIso
      ((CommGrpCat.fullyFaithfulForget₂ToGrp.whiskeringRight (Over S)ᵒᵖ).preimageIso
        (yonedaGrp.mapIso e)))

/-- The represented sheaf isomorphism acts by the original native
group-scheme isomorphism on every point. -/
theorem representedFppfAbIso_apply {S : Scheme.{u}} {G H : Grp (Over S)}
    [IsCommMonObj G.X] [IsCommMonObj H.X] (e : G ≅ H) (U : Over S) (x : U ⟶ G.X) :
    (representedFppfAbIso e).hom.hom.app (Opposite.op U) (ULift.up x) =
      ULift.up (x ≫ e.hom.hom.hom) := rfl

/-- Formation of the represented commutative fppf sheaf commutes with
native pullback of the group scheme. -/
def representedFppfAbBaseChangeIso {S T : Scheme.{u}} (f : T ⟶ S) (G : Grp (Over S))
    [IsCommMonObj G.X] :
    (baseChangeFppfAb f).obj (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) ≅
      @CommutativeSheavesAb.Construction.Schemes.representedFppfAb T ((Over.pullback f).mapGrp.obj G)
        (Functor.isCommMonObj_obj (F := Over.pullback f) (M := G.X)) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (Functor.isoWhiskerRight
      ((CommGrpCat.fullyFaithfulForget₂ToGrp.whiskeringRight (Over T)ᵒᵖ).preimageIso
        (X := (Over.map f).op ⋙ CharacterGroupSheaf.Construction.Schemes.commGroupPoints S G)
        (Y := @CharacterGroupSheaf.Construction.Schemes.commGroupPoints T ((Over.pullback f).mapGrp.obj G)
          (Functor.isCommMonObj_obj (F := Over.pullback f) (M := G.X)))
        (CharacterBaseChange.Construction.Schemes.pullbackGroupPointIso f G)) CommGrpCat.uliftFunctor.{u + 1, u})

/-- The multiplicative fppf sheaf has its canonical arbitrary-base-change isomorphism. -/
def multiplicativeFppfAbBaseChangeIso {S T : Scheme.{u}} (f : T ⟶ S) :
    (baseChangeFppfAb f).obj (CommutativeSheavesAb.Construction.Schemes.multiplicativeFppfAb S) ≅ CommutativeSheavesAb.Construction.Schemes.multiplicativeFppfAb T := by
  let hc : IsCommMonObj ((Over.pullback f).mapGrp.obj (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S)).X :=
    Functor.isCommMonObj_obj (F := Over.pullback f) (M := (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X)
  exact representedFppfAbBaseChangeIso f (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) ≪≫
    @representedFppfAbIso T _ _ hc (CharacterGroupSheaf.Construction.Schemes.multiplicativeGroupOver_commutative T)
      (SliceCharacters.Construction.Schemes.multiplicativeGroup_pullbackIso f)

/-- The actual Cartier-dual character sheaf commutes with arbitrary
base change for every commutative fppf sheaf. -/
def sheafDualBaseChangeIso {S T : Scheme.{u}} (f : T ⟶ S) (G : CommutativeSheavesAb.Construction.Schemes.FppfAb S) :
    (baseChangeFppfAb f).obj (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G) ≅
      CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf ((baseChangeFppfAb f).obj G) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (CommutativeSheaves.internalHomWhiskerIso (Over.map f)
      (G.obj ⋙ forget₂ CommGrpCat GrpCat) (CommutativeSheavesAb.Construction.Schemes.multiplicativeFppfAb S).obj ≪≫
      CommutativeSheaves.internalHomCongr (Iso.refl _)
        ((sheafToPresheaf _ _).mapIso (multiplicativeFppfAbBaseChangeIso f)))

end Schemes

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafBaseChange
