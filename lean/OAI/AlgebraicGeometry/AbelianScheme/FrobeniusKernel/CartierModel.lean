import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterGroups
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.RepresentedGroups
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.AnnihilatorSheaf
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BaseChange
import OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineSheafIso

/-! # Cartier Model -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierModel.Construction

noncomputable section

/-!
Construct the actual Cartier group and its restriction maps from CartierDuality's
checked finite Hopf presentation and character-sheaf representation. The
group law is recovered from pointwise character multiplication, so no
group-compatibility or annihilator-representation conclusion is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj IsMulCommutative

universe u

structure CartierCoordinates (R : CommRingCat.{u}) (G : Grp (Over (Spec R))) where
  algebra : CommHopfAlgCat R
  finite : Module.Finite R algebra
  projective : Module.Projective R algebra
  cocommutative : Coalgebra.IsCocomm R algebra
  comparison : (hopfSpec R).obj (op algebra) ≅ G

attribute [instance] CartierCoordinates.finite CartierCoordinates.projective
  CartierCoordinates.cocommutative

/-- The coordinate presentation is extracted from actual finite flat
commutative group-scheme hypotheses using CartierDuality. -/
def cartierCoordinates (R : CommRingCat.{u}) (G : Grp (Over (Spec R)))
    [IsCommMonObj G.X] [IsFinite G.X.hom] [Flat G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] : CartierCoordinates R G :=
  Classical.choice (by
    obtain ⟨A, hf, hp, hc, ⟨e⟩⟩ := CartierDuality.PolarizedTorsion.Construction.exists_finiteProjective_commutative_hopfPresentation R G
    exact ⟨⟨A, hf, hp, hc, e⟩⟩)

namespace CartierCoordinates

variable {R : CommRingCat.{u}} {G H : Grp (Over (Spec R))}

/-- The representing scheme is the spectrum of the constructed dual Hopf algebra. -/
abbrev dualScheme (P : CartierCoordinates R G) : Over (Spec R) :=
  (Spec (.of (CartierDuality.DualAlgebra.Construction.DualCoordinate R P.algebra))).asOver (Spec R)

/-- CartierDuality's canonical map is an isomorphism on every fppf test scheme. -/
def characterIso (P : CartierCoordinates R G) :
    (BaseChange.Construction.fppfPoints (Spec R)).obj P.dualScheme ≅ CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec R) G := by
  let e := @asIso _ _ _ _ (CartierDuality.CharacterMap.Construction.affineCartierCharacterSheafMap R P.algebra)
    (CartierDuality.AffineSheafIso.Construction.affineCartierCharacterSheafMap_isIso R P.algebra)
  exact e ≪≫ AnnihilatorSheaf.Construction.characterSheafIso P.comparison

def characterRepresentation (P : CartierCoordinates R G) :
    (CharacterGroups.Construction.characterGroupPresheaf G ⋙ forget GrpCat).RepresentableBy P.dualScheme :=
  (Functor.RepresentableBy.equivUliftYonedaIso
    (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec R) G).obj P.dualScheme).symm
      ((sheafToPresheaf _ _).mapIso P.characterIso)

/-- The Cartier group law is constructed from actual multiplication of
characters on the representing scheme. -/
abbrev dualGroup (P : CartierCoordinates R G) : Grp (Over (Spec R)) :=
  RepresentedGroups.Construction.representedGroup (CharacterGroups.Construction.characterGroupPresheaf G) P.dualScheme P.characterRepresentation

def pointsEquiv (P : CartierCoordinates R G) (T : Over (Spec R)) :
    (T ⟶ P.dualGroup.X) ≃* CharacterGroups.Construction.CharacterSections G T :=
  RepresentedGroups.Construction.representedGroupPoints (CharacterGroups.Construction.characterGroupPresheaf G) P.dualScheme P.characterRepresentation T

instance dualGroup_commutative (P : CartierCoordinates R G) : IsCommMonObj P.dualGroup.X := by
  have : ∀ T, IsMulCommutative ((CharacterGroups.Construction.characterGroupPresheaf G).obj T) := fun T =>
    inferInstanceAs (IsMulCommutative (CharacterGroups.Construction.CharacterSections G T.unop))
  exact RepresentedGroups.Construction.representedGroup_commutative _ _ _

theorem dualGroup_finiteLocallyFree (P : CartierCoordinates R G) :
    IsFinite P.dualGroup.X.hom ∧ Flat P.dualGroup.X.hom ∧
      LocallyOfFinitePresentation P.dualGroup.X.hom :=
  CartierDuality.PolarizedTorsion.Construction.dualCoordinateScheme_finiteLocallyFree R P.algebra

instance dualGroup_finite (P : CartierCoordinates R G) : IsFinite P.dualGroup.X.hom :=
  P.dualGroup_finiteLocallyFree.1

instance dualGroup_flat (P : CartierCoordinates R G) : Flat P.dualGroup.X.hom :=
  P.dualGroup_finiteLocallyFree.2.1

instance dualGroup_finitelyPresented (P : CartierCoordinates R G) :
    LocallyOfFinitePresentation P.dualGroup.X.hom := P.dualGroup_finiteLocallyFree.2.2

/-- Restricting a character along the chosen subgroup gives an actual
homomorphism of the constructed Cartier group schemes. -/
def restriction (P : CartierCoordinates R G) (Q : CartierCoordinates R H) (i : H ⟶ G) :
    P.dualGroup ⟶ Q.dualGroup := by
  let f : P.dualGroup.X ⟶ Q.dualGroup.X :=
    RepresentedGroups.Construction.representedGroupMap P.characterRepresentation Q.characterRepresentation (CharacterGroups.Construction.characterGroupRestriction i)
  have : IsMonHom f :=
    RepresentedGroups.Construction.representedGroupMap_isMonHom P.characterRepresentation Q.characterRepresentation
      (CharacterGroups.Construction.characterGroupRestriction i)
  exact Grp.homMk f

theorem restriction_on_characters (P : CartierCoordinates R G) (Q : CartierCoordinates R H)
    (i : H ⟶ G) (T : Over (Spec R)) (x : T ⟶ P.dualGroup.X) :
    Q.pointsEquiv T (x ≫ (P.restriction Q i).hom.hom) =
      Functor.whiskerLeft (Over.forget T).op (yonedaGrp.map i) ≫ P.pointsEquiv T x := by
  exact RepresentedGroups.Construction.representedGroupMap_action P.characterRepresentation Q.characterRepresentation
    (CharacterGroups.Construction.characterGroupRestriction i) x

end CartierCoordinates

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierModel.Construction
