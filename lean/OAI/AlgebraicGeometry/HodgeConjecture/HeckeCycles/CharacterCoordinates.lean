import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineCharacterGroups
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Evaluation

/-! # Character Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CharacterCoordinates.CM

noncomputable section

/-! Identify base-valued points of an actual Cartier representative with
native scheme characters and with group-like Hopf coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

def pullbackIdentityGroup {S : Scheme.{u}} (G : Grp (Over S)) :
    (Over.pullback (𝟙 S)).mapGrp.obj G ≅ G :=
  (Functor.mapGrpNatIso Over.pullbackId).app G ≪≫ Functor.mapGrpIdIso.app G

def baseSectionsEquiv (S : Scheme.{u}) (G : Grp (Over S)) :
    (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (.op (Over.mk (𝟙 S))) ≃*
      (G ⟶ AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) :=
  (AbelianScheme.CartierDuality.CharacterMultiplicationMul.Construction.Schemes.testCharacterMulEquiv S G (Over.mk (𝟙 S))).trans
    (AbelianScheme.CartierDuality.CharacterMultiplicationMul.Construction.CharacterMultiplication.homCongrMulEquiv (pullbackIdentityGroup G) (Iso.refl _))

def representativePointsEquiv {S : Scheme.{u}} {G : Grp (Over S)}
    (C : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) :
    (Over.mk (𝟙 S) ⟶ C.dual.X) ≃* (G ⟶ AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) :=
  (C.sectionEquiv (Over.mk (𝟙 S))).trans (baseSectionsEquiv S G)

def coordinateCharactersEquiv (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) (R : CommHopfAlgCat k)
    (e : (hopfSpec (.of k)).obj (.op R) ≅ G) :
    (G ⟶ AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))) ≃* GroupLike k R :=
  (AbelianScheme.CartierDuality.CharacterMultiplicationMul.Construction.CharacterMultiplication.homCongrMulEquiv e.symm (AbelianScheme.CartierDuality.AffinePullback.Construction.Schemes.multiplicativeGroupOverSpecIso k)).trans
    (AbelianScheme.CartierDuality.AffineCharacterGroups.Construction.groupLikeMulEquivSchemeCharacters k R).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CharacterCoordinates.CM
