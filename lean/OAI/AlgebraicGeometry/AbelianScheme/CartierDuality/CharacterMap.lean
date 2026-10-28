import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffinePullback
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineCharacterValues
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Naturality

/-! # Character Map -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterMap.Construction

noncomputable section

/-!
# CartierDuality: the universal character and the canonical sheaf morphism

The map is defined on all test schemes by pulling back a universal
character. Its naturality is part of its construction via Yoneda.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

variable (R A : Type u) [CommRing R] [CommRing A]
variable [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
variable [Module.Finite R A] [Module.Projective R A]

/-- The universal character is induced by the group-like coevaluation
element of the dual coordinate algebra. -/
def affineCartierUniversalCharacter :
    (CharacterSheaf.Construction.Schemes.characterSheaf (Spec (CommRingCat.of R)) (Characters.Construction.affineHopfGroupScheme R A)).obj.obj
      (Opposite.op ((Spec (CommRingCat.of (DualAlgebra.Construction.DualCoordinate R A))).asOver (Spec (CommRingCat.of R)))) :=
  AffineCharacterValues.Construction.affineGroupLikeSection R (DualAlgebra.Construction.DualCoordinate R A) A (Naturality.Construction.universalAffineCharacter R A)

/-- The canonical comparison on all test schemes is obtained by pulling
back the universal character. -/
def affineCartierCharacterMap :
    uliftYoneda.{u + 1}.obj ((Spec (CommRingCat.of (DualAlgebra.Construction.DualCoordinate R A))).asOver (Spec (CommRingCat.of R))) ⟶
      (CharacterSheaf.Construction.Schemes.characterSheaf (Spec (CommRingCat.of R)) (Characters.Construction.affineHopfGroupScheme R A)).obj :=
  uliftYonedaEquiv.symm (affineCartierUniversalCharacter R A)

/-- The represented point sheaf of the constructed affine dual. The
universe lift matches the character sheaf on the big fppf site. -/
def affineDualPointSheaf :
    Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1)) :=
  ⟨uliftYoneda.{u + 1}.obj ((Spec (CommRingCat.of (DualAlgebra.Construction.DualCoordinate R A))).asOver (Spec (CommRingCat.of R))), by
    rw [isSheaf_iff_isSheaf_of_type]
    exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _⟩

/-- The actual sheaf comparison, defined independently of any
representability assertion about the target character sheaf. -/
def affineCartierCharacterSheafMap :
    affineDualPointSheaf R A ⟶
      CharacterSheaf.Construction.Schemes.characterSheaf (Spec (CommRingCat.of R)) (Characters.Construction.affineHopfGroupScheme R A) :=
  ⟨affineCartierCharacterMap R A⟩

/-- Evaluation at any test point is restriction of the universal character. -/
theorem affineCartierCharacterMap_apply
    (T : Over (Spec (CommRingCat.of R)))
    (f : T ⟶ ((Spec (CommRingCat.of (DualAlgebra.Construction.DualCoordinate R A))).asOver (Spec (CommRingCat.of R)))) :
    (affineCartierCharacterMap R A).app (Opposite.op T) (ULift.up f) =
      (CharacterSheaf.Construction.Schemes.characterSheaf (Spec (CommRingCat.of R))
        (Characters.Construction.affineHopfGroupScheme R A)).obj.map f.op (affineCartierUniversalCharacter R A) :=
  rfl

/-- The canonical comparison acts by pulling back the universal evaluation
morphism on the product with G. -/
theorem affineCartierCharacterMap_value
    (T : Over (Spec (CommRingCat.of R)))
    (f : T ⟶ ((Spec (CommRingCat.of (DualAlgebra.Construction.DualCoordinate R A))).asOver (Spec (CommRingCat.of R)))) :
    SliceCharacters.Construction.Schemes.characterValue (Spec (CommRingCat.of R)) (Characters.Construction.affineHopfGroupScheme R A) T
      ((affineCartierCharacterMap R A).app (Opposite.op T) (ULift.up f)) =
    Limits.prod.map f (𝟙 (Characters.Construction.affineHopfGroupScheme R A).X) ≫
      SliceCharacters.Construction.Schemes.characterValue (Spec (CommRingCat.of R)) (Characters.Construction.affineHopfGroupScheme R A)
        ((Spec (CommRingCat.of (DualAlgebra.Construction.DualCoordinate R A))).asOver (Spec (CommRingCat.of R)))
        (affineCartierUniversalCharacter R A) :=
  SliceCharacters.Construction.Schemes.characterValue_restrict (Spec (CommRingCat.of R)) (Characters.Construction.affineHopfGroupScheme R A)
    f (affineCartierUniversalCharacter R A)

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterMap.Construction
