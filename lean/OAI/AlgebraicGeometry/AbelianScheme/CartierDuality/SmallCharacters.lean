import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterBaseChange

/-! # Small Characters -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SmallCharacters.Construction

noncomputable section

/-!
# CartierDuality: a small-valued model of the character sheaf

The big-site internal Hom initially takes values in a larger universe.
Native morphisms over each test scheme give an equivalent small-valued
sheaf, so ordinary scheme representability and gluing results can apply.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

namespace CharacterSize

universe v w

variable {C : Type w} [Category.{v} C]

/-- Transport a type-valued functor through small models of its values. -/
def downsizeFunctor (F : C ⥤ Type (u + 1)) (B : C → Type u)
    (e : ∀ X, F.obj X ≃ B X) : C ⥤ Type u where
  obj := B
  map {X Y} f := ↾(fun b => e Y (F.map f ((e X).symm b)))
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro b
    exact (congrArg (e X) (F.map_id_apply X ((e X).symm b))).trans
      ((e X).apply_symm_apply b)
  map_comp {X Y Z} f g := by
    apply ConcreteCategory.hom_ext
    intro b
    change e Z (F.map (f ≫ g) ((e X).symm b)) =
      e Z (F.map g ((e Y).symm (e Y (F.map f ((e X).symm b)))))
    simp only [Equiv.symm_apply_apply, Functor.map_comp_apply]

/-- Lifting a transported small functor recovers the original functor. -/
def downsizeFunctorIso (F : C ⥤ Type (u + 1)) (B : C → Type u)
    (e : ∀ X, F.obj X ≃ B X) :
    downsizeFunctor F B e ⋙ uliftFunctor.{u + 1} ≅ F :=
  NatIso.ofComponents (fun X => (Equiv.ulift.trans (e X).symm).toIso) (by
    intro X Y f
    apply ConcreteCategory.hom_ext
    intro b
    exact (e Y).symm_apply_apply _)

end CharacterSize

namespace Schemes

variable (S : Scheme.{u}) (G : Grp (Over S))

/-- Every character-section type is small because its sections are
ordinary morphisms of group schemes over the test scheme. -/
instance characterSectionsSmall (T : Over S) :
    Small.{u} ((CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T)) :=
  small_of_injective (SliceCharacters.Construction.Schemes.characterSheaf_testCharacterEquiv S G T).injective

/-- Characters expressed as native group-scheme homomorphisms, with
restriction transported from the actual internal Hom presheaf. -/
def nativeCharacterPresheaf : (Over S)ᵒᵖ ⥤ Type u :=
  CharacterSize.downsizeFunctor (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj
    (fun T => (Over.pullback T.unop.hom).mapGrp.obj G ⟶ CharacterSheaf.Construction.Schemes.multiplicativeGroupOver T.unop.left)
    (fun T => SliceCharacters.Construction.Schemes.characterSheaf_testCharacterEquiv S G T.unop)

/-- Lifting the native character presheaf recovers the original
big-site character presheaf, naturally on all test schemes. -/
def nativeCharacterPresheafIso :
    nativeCharacterPresheaf S G ⋙ uliftFunctor.{u + 1} ≅ (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj :=
  CharacterSize.downsizeFunctorIso (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj
    (fun T => (Over.pullback T.unop.hom).mapGrp.obj G ⟶ CharacterSheaf.Construction.Schemes.multiplicativeGroupOver T.unop.left)
    (fun T => SliceCharacters.Construction.Schemes.characterSheaf_testCharacterEquiv S G T.unop)

/-- The native small-valued model satisfies fppf descent. -/
theorem nativeCharacterPresheaf_isSheaf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (nativeCharacterPresheaf S G) := by
  apply Presheaf.isSheaf_of_isSheaf_comp (Scheme.fppfTopology.over S)
    (nativeCharacterPresheaf S G) uliftFunctor.{u + 1}
  exact (Presheaf.isSheaf_of_iso_iff (nativeCharacterPresheafIso S G)).mpr
    (CharacterSheaf.Construction.Schemes.characterSheaf S G).property

/-- A small-valued fppf character sheaf suitable for native scheme
representability and gluing constructions. -/
def nativeCharacterSheaf : Sheaf (Scheme.fppfTopology.over S) (Type u) :=
  ⟨nativeCharacterPresheaf S G, nativeCharacterPresheaf_isSheaf S G⟩

end Schemes

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SmallCharacters.Construction
