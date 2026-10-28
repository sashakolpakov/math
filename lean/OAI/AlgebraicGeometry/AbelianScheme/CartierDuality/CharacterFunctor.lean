import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterSheaf
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Character Functor -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterFunctor.Construction.Schemes

noncomputable section

/-!
# CartierDuality: functoriality of character sheaves
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- Restriction along the identity leaves every character unchanged. -/
theorem characterRestriction_id (S : Scheme.{u}) (G : Grp (Over S)) :
    CharacterSheaf.Construction.Schemes.characterRestriction (𝟙 G) = 𝟙 (CharacterSheaf.Construction.Schemes.characterSheaf S G) := by
  ext T χ
  apply NatTrans.ext
  funext U
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  change χ.app U (x ≫ 𝟙 G.X) = χ.app U x
  exact congrArg (fun f => χ.app U f) (Category.comp_id x)

/-- Restriction along a composite is successive restriction. -/
theorem characterRestriction_comp {S : Scheme.{u}} {H G K : Grp (Over S)}
    (i : H ⟶ G) (j : G ⟶ K) :
    CharacterSheaf.Construction.Schemes.characterRestriction (i ≫ j) = CharacterSheaf.Construction.Schemes.characterRestriction j ≫ CharacterSheaf.Construction.Schemes.characterRestriction i := by
  ext T χ
  apply NatTrans.ext
  funext U
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  change χ.app U (x ≫ (i.hom.hom ≫ j.hom.hom)) =
    χ.app U ((x ≫ i.hom.hom) ≫ j.hom.hom)
  exact congrArg (fun f => χ.app U f) (Category.assoc x i.hom.hom j.hom.hom).symm

/-- The fppf character construction is contravariantly functorial in
the source group scheme. -/
def characterSheafFunctor (S : Scheme.{u}) :
    (Grp (Over S))ᵒᵖ ⥤ Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) where
  obj G := CharacterSheaf.Construction.Schemes.characterSheaf S G.unop
  map f := CharacterSheaf.Construction.Schemes.characterRestriction f.unop
  map_id G := characterRestriction_id S G.unop
  map_comp f g := characterRestriction_comp g.unop f.unop

/-- A group-scheme isomorphism induces an isomorphism of its actual
character sheaves by restriction. -/
def characterSheafIso {S : Scheme.{u}} {G H : Grp (Over S)} (e : G ≅ H) :
    CharacterSheaf.Construction.Schemes.characterSheaf S H ≅ CharacterSheaf.Construction.Schemes.characterSheaf S G :=
  (characterSheafFunctor S).mapIso e.op

/-- The fppf sheaf of points of a scheme over S, with the universe lift
used by the character sheaf. -/
def pointSheaf (S : Scheme.{u}) (X : Over S) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  ⟨uliftYoneda.{u + 1}.obj X, by
    rw [isSheaf_iff_isSheaf_of_type]
    exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _⟩

/-- Finite locally free representability asks for an actual representing
scheme with a finite, flat, locally finitely presented structure morphism. -/
def FiniteLocallyFreeRepresentable {S : Scheme.{u}}
    (F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))) : Prop :=
  ∃ X : Over S, IsFinite X.hom ∧ Flat X.hom ∧ LocallyOfFinitePresentation X.hom ∧
    Nonempty (pointSheaf S X ≅ F)

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterFunctor.Construction.Schemes
