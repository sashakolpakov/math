import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SmallCharacters
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.Algebra.Group.TransferInstance

/-! # Character Group Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterGroupSheaf

noncomputable section

/-!
# CartierDuality: the commutative group structure on the actual character sheaf
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u v w

namespace Construction

namespace CharacterGroups

variable {C : Type u} [Category.{v} C] (F : C ⥤ GrpCat.{w}) (K : C ⥤ CommGrpCat.{w})

/-- Pointwise identity natural transformation into commutative groups. -/
def one : F ⟶ K ⋙ forget₂ CommGrpCat GrpCat where
  app X := GrpCat.ofHom 1
  naturality := by
    intro X Y f
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact ((K.map f).hom.map_one).symm

/-- Pointwise product of natural group homomorphisms. -/
def mul (a b : F ⟶ K ⋙ forget₂ CommGrpCat GrpCat) :
    F ⟶ K ⋙ forget₂ CommGrpCat GrpCat where
  app X := GrpCat.ofHom ((a.app X).hom * (b.app X).hom)
  naturality := by
    intro X Y f
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    change a.app Y (F.map f x) * b.app Y (F.map f x) =
      K.map f (a.app X x * b.app X x)
    exact (congrArg₂ (fun p q : K.obj Y => p * q)
      (a.naturality_apply f x) (b.naturality_apply f x)).trans
        ((K.map f).hom.map_mul _ _).symm

/-- Pointwise inverse of a natural group homomorphism. -/
def inv (a : F ⟶ K ⋙ forget₂ CommGrpCat GrpCat) :
    F ⟶ K ⋙ forget₂ CommGrpCat GrpCat where
  app X := GrpCat.ofHom (a.app X).hom⁻¹
  naturality := by
    intro X Y f
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    change (a.app Y (F.map f x))⁻¹ = K.map f (a.app X x)⁻¹
    exact (congrArg (fun p : K.obj Y => p⁻¹) (a.naturality_apply f x)).trans
      (map_inv (K.map f).hom _).symm

/-- Natural group homomorphisms into commutative groups form a
commutative group under pointwise operations. -/
instance homCommGroup : CommGroup (F ⟶ K ⋙ forget₂ CommGrpCat GrpCat) where
  one := CharacterGroups.one F K
  mul := CharacterGroups.mul F K
  inv := CharacterGroups.inv F K
  mul_assoc a b c := by
    apply NatTrans.ext
    funext X
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact mul_assoc _ _ _
  one_mul a := by
    apply NatTrans.ext
    funext X
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact one_mul _
  mul_one a := by
    apply NatTrans.ext
    funext X
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact mul_one _
  inv_mul_cancel a := by
    apply NatTrans.ext
    funext X
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact inv_mul_cancel _
  mul_comm a b := by
    apply NatTrans.ext
    funext X
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact @mul_comm (K.obj X) inferInstance (a.app X x) (b.app X x)

end CharacterGroups

namespace CharacterSize

variable {C : Type v} [Category.{w} C]

/-- Transport a commutative-group presheaf through small models of its
values while retaining the transported restriction maps. -/
def downsizeCommGroupFunctor (F : C ⥤ CommGrpCat.{u + 1}) (B : C → Type u)
    (e : ∀ X, F.obj X ≃ B X) : C ⥤ CommGrpCat.{u} := by
  let (X : C) : CommGroup (B X) := (e X).symm.commGroup
  refine
    { obj X := CommGrpCat.of (B X)
      map := fun {X Y} f => CommGrpCat.ofHom
        (((e Y).symm.mulEquiv).symm.toMonoidHom.comp
          ((F.map f).hom.comp ((e X).symm.mulEquiv).toMonoidHom))
      map_id := ?_
      map_comp := ?_ }
  · intro X
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro b
    change e X (F.map (𝟙 X) ((e X).symm b)) = b
    exact (congrArg (e X) (F.map_id_apply X ((e X).symm b))).trans
      ((e X).apply_symm_apply b)
  · intro X Y Z f g
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro b
    change e Z (F.map (f ≫ g) ((e X).symm b)) =
      e Z (F.map g ((e Y).symm (e Y (F.map f ((e X).symm b)))))
    simp only [Equiv.symm_apply_apply, Functor.map_comp_apply]

/-- Forgetting the transported groups recovers the transported
type-valued functor without changing any maps. -/
theorem downsizeCommGroupFunctor_forget (F : C ⥤ CommGrpCat.{u + 1}) (B : C → Type u)
    (e : ∀ X, F.obj X ≃ B X) :
    downsizeCommGroupFunctor F B e ⋙ forget CommGrpCat =
      SmallCharacters.Construction.CharacterSize.downsizeFunctor (F ⋙ forget CommGrpCat) B e := rfl

/-- The transported small group is multiplicatively equivalent to the
original group at each test object. -/
def downsizeCommGroupEquiv (F : C ⥤ CommGrpCat.{u + 1}) (B : C → Type u)
    (e : ∀ X, F.obj X ≃ B X) (X : C) :
    (downsizeCommGroupFunctor F B e).obj X ≃* F.obj X :=
  (e X).symm.mulEquiv

/-- The component group equivalences commute with all restriction maps. -/
theorem downsizeCommGroupEquiv_map (F : C ⥤ CommGrpCat.{u + 1}) (B : C → Type u)
    (e : ∀ X, F.obj X ≃ B X) {X Y : C} (f : X ⟶ Y)
    (b : (downsizeCommGroupFunctor F B e).obj X) :
    downsizeCommGroupEquiv F B e Y ((downsizeCommGroupFunctor F B e).map f b) =
      F.map f (downsizeCommGroupEquiv F B e X b) :=
  (e Y).symm_apply_apply _

end CharacterSize

namespace Schemes

/-- The global multiplicative group is commutative. -/
instance multiplicativeGroupOver_commutative (S : Scheme.{u}) :
    IsCommMonObj (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X := by
  let R := ULift.{u} ℤ
  let : IsCommMonObj (Characters.Construction.multiplicativeGroupScheme R).X :=
    inferInstanceAs (IsCommMonObj
      ((Spec (CommRingCat.of (Characters.Construction.MultiplicativeGroupCoordinate R))).asOver (Spec (CommRingCat.of R))))
  exact Functor.isCommMonObj_obj
    (F := Over.pullback (specULiftZIsTerminal.from S)) (M := (Characters.Construction.multiplicativeGroupScheme R).X)

/-- Group-valued points of a commutative group scheme, with their
commutative group structure retained in the codomain. -/
def commGroupPoints (S : Scheme.{u}) (K : Grp (Over S)) [IsCommMonObj K.X] :
    (Over S)ᵒᵖ ⥤ CommGrpCat.{u} where
  obj T := CommGrpCat.of (T.unop ⟶ K.X)
  map f := CommGrpCat.ofHom (((yonedaGrp.obj K).map f).hom)

/-- Forgetting commutativity gives the original group-valued points. -/
theorem commGroupPoints_forget (S : Scheme.{u}) (K : Grp (Over S)) [IsCommMonObj K.X] :
    commGroupPoints S K ⋙ forget₂ CommGrpCat GrpCat = yonedaGrp.obj K := rfl

/-- Characters over each test scheme form a commutative group, using
pointwise multiplication of the actual natural group homomorphisms. -/
instance characterSectionsCommGroup (S : Scheme.{u}) (G : Grp (Over S)) (T : (Over S)ᵒᵖ) :
    CommGroup ((CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj T) :=
  CharacterGroups.homCommGroup ((Over.forget T.unop).op ⋙ yonedaGrp.obj G)
    ((Over.forget T.unop).op ⋙ commGroupPoints S (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S))

/-- The actual internal character Hom, upgraded to a commutative-group
presheaf with its original restriction maps. -/
def characterCommGroupPresheaf (S : Scheme.{u}) (G : Grp (Over S)) :
    (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1} where
  obj T := CommGrpCat.of ((CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj T)
  map f := CommGrpCat.ofHom
    { toFun := (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.map f
      map_one' := rfl
      map_mul' _ _ := rfl }
  map_id T := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro χ
    exact (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.map_id_apply T χ
  map_comp f g := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro χ
    exact (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.map_comp_apply f g χ

/-- The upgraded presheaf has exactly the original underlying character
presheaf, including all restriction maps. -/
theorem characterCommGroupPresheaf_forget (S : Scheme.{u}) (G : Grp (Over S)) :
    characterCommGroupPresheaf S G ⋙ forget CommGrpCat = (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj := rfl

/-- The small character presheaf, retaining the pointwise commutative
group structure of the original internal Hom. -/
def nativeCharacterCommGroupPresheaf (S : Scheme.{u}) (G : Grp (Over S)) :
    (Over S)ᵒᵖ ⥤ CommGrpCat.{u} :=
  CharacterSize.downsizeCommGroupFunctor (characterCommGroupPresheaf S G)
    (fun T => (Over.pullback T.unop.hom).mapGrp.obj G ⟶ CharacterSheaf.Construction.Schemes.multiplicativeGroupOver T.unop.left)
    (fun T => SliceCharacters.Construction.Schemes.characterSheaf_testCharacterEquiv S G T.unop)

/-- The small commutative-group presheaf has the previously constructed
native character presheaf as its exact underlying presheaf. -/
theorem nativeCharacterCommGroupPresheaf_forget (S : Scheme.{u}) (G : Grp (Over S)) :
    nativeCharacterCommGroupPresheaf S G ⋙ forget CommGrpCat =
      SmallCharacters.Construction.Schemes.nativeCharacterPresheaf S G := rfl

/-- Native character groups and original internal-Hom sections are
equivalent as groups, by the chosen size comparison. -/
def nativeCharacterSectionsMulEquiv (S : Scheme.{u}) (G : Grp (Over S)) (T : (Over S)ᵒᵖ) :
    (nativeCharacterCommGroupPresheaf S G).obj T ≃* (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj T :=
  CharacterSize.downsizeCommGroupEquiv (characterCommGroupPresheaf S G)
    (fun U => (Over.pullback U.unop.hom).mapGrp.obj G ⟶ CharacterSheaf.Construction.Schemes.multiplicativeGroupOver U.unop.left)
    (fun U => SliceCharacters.Construction.Schemes.characterSheaf_testCharacterEquiv S G U.unop) T

/-- The group-valued size comparison respects the original character
restriction maps. -/
theorem nativeCharacterSectionsMulEquiv_natural (S : Scheme.{u}) (G : Grp (Over S))
    {T U : (Over S)ᵒᵖ} (f : T ⟶ U) (χ : (nativeCharacterCommGroupPresheaf S G).obj T) :
    nativeCharacterSectionsMulEquiv S G U ((nativeCharacterCommGroupPresheaf S G).map f χ) =
      (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.map f (nativeCharacterSectionsMulEquiv S G T χ) :=
  CharacterSize.downsizeCommGroupEquiv_map (characterCommGroupPresheaf S G)
    (fun V => (Over.pullback V.unop.hom).mapGrp.obj G ⟶ CharacterSheaf.Construction.Schemes.multiplicativeGroupOver V.unop.left)
    (fun V => SliceCharacters.Construction.Schemes.characterSheaf_testCharacterEquiv S G V.unop) f χ

/-- The actual character presheaf satisfies fppf descent with its
commutative-group structure, as well as after forgetting that structure. -/
def characterCommGroupSheaf (S : Scheme.{u}) (G : Grp (Over S)) :
    Sheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1} :=
  ⟨characterCommGroupPresheaf S G,
    Presheaf.isSheaf_of_isSheaf_comp (Scheme.fppfTopology.over S)
      (characterCommGroupPresheaf S G) (forget CommGrpCat) (CharacterSheaf.Construction.Schemes.characterSheaf S G).property⟩

/-- A small-valued fppf sheaf of commutative groups whose sections are
native characters and whose restrictions are the actual character restrictions. -/
def nativeCharacterCommGroupSheaf (S : Scheme.{u}) (G : Grp (Over S)) :
    Sheaf (Scheme.fppfTopology.over S) CommGrpCat.{u} :=
  ⟨nativeCharacterCommGroupPresheaf S G,
    Presheaf.isSheaf_of_isSheaf_comp (Scheme.fppfTopology.over S)
      (nativeCharacterCommGroupPresheaf S G) (forget CommGrpCat)
        (SmallCharacters.Construction.Schemes.nativeCharacterPresheaf_isSheaf S G)⟩

end Schemes

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterGroupSheaf
