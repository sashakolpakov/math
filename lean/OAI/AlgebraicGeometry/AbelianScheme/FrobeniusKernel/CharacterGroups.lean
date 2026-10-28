import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryCharacters
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterSheaf

/-! # Character Groups -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterGroups.Construction

noncomputable section

/-!
Characters carry their actual pointwise commutative group law. The group
law is constructed before representability is used; it therefore recovers
the Cartier group law on a representing scheme without an assumed group
comparison.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj IsMulCommutative

universe u v w

variable {C : Type u} [Category.{v} C]

def characterNatMul (G K : C ⥤ GrpCat.{w}) [∀ X, IsMulCommutative (K.obj X)]
    (a b : G ⟶ K) : G ⟶ K where
  app X := GrpCat.ofHom ((a.app X).hom * (b.app X).hom)
  naturality := by
    intro X Y f
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    change a.app Y (G.map f x) * b.app Y (G.map f x) = K.map f (a.app X x * b.app X x)
    exact (congrArg₂ (· * ·) (a.naturality_apply f x) (b.naturality_apply f x)).trans
      ((K.map f).hom.map_mul _ _).symm

def characterNatInv (G K : C ⥤ GrpCat.{w}) [∀ X, IsMulCommutative (K.obj X)]
    (a : G ⟶ K) : G ⟶ K where
  app X := GrpCat.ofHom ((a.app X).hom⁻¹)
  naturality := by
    intro X Y f
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    change (a.app Y (G.map f x))⁻¹ = K.map f ((a.app X x)⁻¹)
    exact (congrArg Inv.inv (a.naturality_apply f x)).trans
      ((K.map f).hom.map_inv _).symm

instance characterNatCommGroup (G K : C ⥤ GrpCat.{w})
    [∀ X, IsMulCommutative (K.obj X)] : CommGroup (G ⟶ K) where
  one := CartierDuality.CharacterSheaf.Construction.Schemes.trivialGroupNatTrans G K
  mul := characterNatMul G K
  inv := characterNatInv G K
  mul_assoc a b c := by ext X x; exact mul_assoc _ _ _
  one_mul a := by ext X x; exact one_mul _
  mul_one a := by ext X x; exact mul_one _
  inv_mul_cancel a := by ext X x; exact inv_mul_cancel _
  mul_comm a b := by ext X x; exact mul_comm _ _

def characterNatPrecompose {F G K : C ⥤ GrpCat.{w}}
    [∀ X, IsMulCommutative (K.obj X)] (i : F ⟶ G) : (G ⟶ K) →* (F ⟶ K) where
  toFun a := i ≫ a
  map_one' := by ext X x; rfl
  map_mul' a b := by ext X x; rfl

variable {S : Scheme.{u}}

instance characterTarget_comm (T : Over S) (U : (Over T)ᵒᵖ) :
    IsMulCommutative
      (((Over.forget T).op ⋙ yonedaGrp.obj (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S)).obj U) := by
  let G := CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S
  have : IsCommMonObj G.X := by
    let M := CartierDuality.Characters.Construction.multiplicativeGroupScheme (ULift.{u} ℤ)
    have : IsCommMonObj M.X := inferInstanceAs
      (IsCommMonObj ((Spec (.of (CartierDuality.Characters.Construction.MultiplicativeGroupCoordinate (ULift.{u} ℤ)))).asOver
        (Spec (.of (ULift.{u} ℤ)))))
    exact inferInstanceAs (IsCommMonObj
      ((Over.pullback (specULiftZIsTerminal.from S)).obj M.X))
  exact inferInstanceAs (IsMulCommutative (U.unop.left ⟶ G.X))

abbrev CharacterSections (G : Grp (Over S)) (T : Over S) :=
  ((Over.forget T).op ⋙ yonedaGrp.obj G ⟶
    (Over.forget T).op ⋙ yonedaGrp.obj (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S))

/-- The ordinary character sheaf, retaining the pointwise group law. -/
def characterGroupPresheaf (G : Grp (Over S)) : (Over S)ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj T := GrpCat.of (CharacterSections G T.unop)
  map f := GrpCat.ofHom {
    toFun a := Functor.whiskerLeft (Over.map f.unop).op a
    map_one' := by ext U x; rfl
    map_mul' a b := by ext U x; rfl }
  map_id T := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro a
    exact (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.map_id_apply T a
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro a
    exact (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.map_comp_apply f g a

/-- Restriction of characters is a natural group homomorphism. -/
def characterGroupRestriction {H G : Grp (Over S)} (i : H ⟶ G) :
    characterGroupPresheaf G ⟶ characterGroupPresheaf H where
  app T := GrpCat.ofHom
    (characterNatPrecompose (Functor.whiskerLeft (Over.forget T.unop).op (yonedaGrp.map i)))
  naturality := by
    intro T U f
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro a
    rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterGroups.Construction
