import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierModel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingFromPoints
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Evaluation

/-! # Cartier Pairing -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierPairing

noncomputable section

/-! Construct the scheme bicharacter from the actual FrobeniusKernel Cartier
coordinates. Its value is evaluation of the original represented
character, on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierModel.Construction OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Evaluation.Construction

variable {R : CommRingCat.{u}} {G : Grp (Over (Spec R))} (P : AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates R G)

theorem pointCharacters_natural {T U : Over (Spec R)} (f : U ⟶ T) (b : T ⟶ P.dualGroup.X) :
    P.pointsEquiv U (f ≫ b) =
      (presheafHom (yonedaGrp.obj G) (yonedaGrp.obj (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec R)))).map f.op
        (P.pointsEquiv T b) := P.characterRepresentation.homEquiv_comp f b

def cartierPairValue (T : Over (Spec R)) (a : T ⟶ G.X) (b : T ⟶ P.dualGroup.X) :
    T ⟶ (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec R)).X := AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value (P.pointsEquiv T b) a

theorem cartierPairValue_natural {T U : Over (Spec R)} (f : U ⟶ T)
    (a : T ⟶ G.X) (b : T ⟶ P.dualGroup.X) :
    cartierPairValue P U (f ≫ a) (f ≫ b) = f ≫ cartierPairValue P T a b := by
  simp only [cartierPairValue, pointCharacters_natural]
  exact AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value_natural f (P.pointsEquiv T b) a

theorem cartierPairValue_one_left (T : Over (Spec R)) (b : T ⟶ P.dualGroup.X) :
    cartierPairValue P T 1 b = 1 := (AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value (P.pointsEquiv T b)).map_one

theorem cartierPairValue_one_right (T : Over (Spec R)) (a : T ⟶ G.X) :
    cartierPairValue P T a 1 = 1 := by
  rw [cartierPairValue, (P.pointsEquiv T).map_one]
  rfl

theorem cartierPairValue_mul_left (T : Over (Spec R)) (a c : T ⟶ G.X) (b : T ⟶ P.dualGroup.X) :
    cartierPairValue P T (a * c) b = cartierPairValue P T a b * cartierPairValue P T c b :=
  (AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value (P.pointsEquiv T b)).map_mul a c

theorem cartierPairValue_mul_right (T : Over (Spec R)) (a : T ⟶ G.X) (b c : T ⟶ P.dualGroup.X) :
    cartierPairValue P T a (b * c) = cartierPairValue P T a b * cartierPairValue P T a c := by
  rw [cartierPairValue, (P.pointsEquiv T).map_mul]
  rfl

def cartierPairing : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := G.X) (B := P.dualGroup.X)
    (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec R)).X) :=
  AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.ofPointValues (cartierPairValue P) (cartierPairValue_natural P)
    (cartierPairValue_one_left P) (cartierPairValue_one_right P)
    (cartierPairValue_mul_left P) (cartierPairValue_mul_right P)

theorem cartierPairing_pairValue {T : Over (Spec R)} (a : T ⟶ G.X) (b : T ⟶ P.dualGroup.X) :
    (cartierPairing P).pairValue a b = cartierPairValue P T a b :=
  AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.ofPointValues_pairValue _ _ _ _ _ _ T a b

variable {P} in
theorem character_eq_one_iff (T : Over (Spec R)) (χ : AbelianScheme.FrobeniusKernel.CharacterGroups.Construction.CharacterSections G T) :
    χ = 1 ↔ ∀ (U : Over (Spec R)) (f : U ⟶ T) (a : U ⟶ G.X),
      AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value
        ((presheafHom (yonedaGrp.obj G) (yonedaGrp.obj (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec R)))).map f.op χ) a = 1 := by
  constructor
  · rintro rfl U f a
    rfl
  · intro h
    ext V a
    have he := h V.unop.left V.unop.hom a
    exact (AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value_restrict (F := yonedaGrp.obj G)
      (K := yonedaGrp.obj (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec R))) V.unop.hom χ a).symm.trans he

variable {P} in
theorem restricted_character_eq_one_iff {H : Grp (Over (Spec R))} (i : H ⟶ G)
    (T : Over (Spec R)) (χ : AbelianScheme.FrobeniusKernel.CharacterGroups.Construction.CharacterSections G T) :
    Functor.whiskerLeft (Over.forget T).op (yonedaGrp.map i) ≫ χ = 1 ↔
      ∀ (U : Over (Spec R)) (f : U ⟶ T) (a : U ⟶ H.X),
        AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value
          ((presheafHom (yonedaGrp.obj G) (yonedaGrp.obj (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec R)))).map f.op χ)
          (a ≫ i.hom.hom) = 1 := by
  rw [character_eq_one_iff]
  constructor
  · intro h U f a
    exact (AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value_restrict (F := yonedaGrp.obj G)
      (K := yonedaGrp.obj (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec R))) f χ (a ≫ i.hom.hom)).trans
      ((AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value_restrict (F := yonedaGrp.obj H)
        (K := yonedaGrp.obj (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec R))) f
        (Functor.whiskerLeft (Over.forget T).op (yonedaGrp.map i) ≫ χ) a).symm.trans (h U f a))
  · intro h U f a
    exact (AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value_restrict (F := yonedaGrp.obj H)
      (K := yonedaGrp.obj (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec R))) f
      (Functor.whiskerLeft (Over.forget T).op (yonedaGrp.map i) ≫ χ) a).trans
      ((AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value_restrict (F := yonedaGrp.obj G)
        (K := yonedaGrp.obj (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec R))) f χ
        (a ≫ i.hom.hom)).symm.trans (h U f a))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierPairing
