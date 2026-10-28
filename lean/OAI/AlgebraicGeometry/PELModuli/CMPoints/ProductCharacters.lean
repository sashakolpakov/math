import OAI.AlgebraicGeometry.PELModuli.CMPoints.BaseCharacters
import OAI.AlgebraicGeometry.PELModuli.CMPoints.FlattenTorsionFactors
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterGroupSheaf

/-! # Product Characters -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ProductCharacters

noncomputable section

/-! Characters of a finite product split into the characters of its
factors, naturally on every test object. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {I : Type} [Fintype I]

def piBaseCharactersEquiv {S : Scheme.{0}} (F : I → (Over S)ᵒᵖ ⥤ CommGrpCat) :
    (DualityPairing.cartierCharacters (FlattenTorsionFactors.piGroupFunctor F)).obj (.op (Over.mk (𝟙 S))) ≃
      (∀ i, (DualityPairing.cartierCharacters (F i ⋙ forget₂ CommGrpCat GrpCat)).obj (.op (Over.mk (𝟙 S)))) :=
  (BaseCharacters.baseCharactersEquiv (FlattenTorsionFactors.piGroupFunctor F)).trans
    ((FlattenTorsionFactors.piGroupCharactersEquiv F
      (AbelianScheme.CartierDuality.CharacterGroupSheaf.Construction.Schemes.commGroupPoints S
        (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S))).trans
      (Equiv.piCongrRight (fun i => (BaseCharacters.baseCharactersEquiv (F i ⋙ forget₂ CommGrpCat GrpCat)).symm)))

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ProductCharacters
