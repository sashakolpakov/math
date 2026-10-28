import OAI.AlgebraicGeometry.PELModuli.CMPoints.DualityPairing
import OAI.AlgebraicGeometry.PELModuli.CMPoints.RetractIso

/-! # Character Retracts -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.CharacterRetracts

noncomputable section

/-! Character restriction sends a split retraction to a split
retraction in the opposite direction. An ambient duality compatible
with the projectors therefore restricts to their character blocks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S : Scheme} {F G H : (Over S)ᵒᵖ ⥤ GrpCat}

theorem restrictCharacters_id : DualityPairing.restrictCharacters (𝟙 F) = 𝟙 (DualityPairing.cartierCharacters F) := by
  ext T χ
  rfl

theorem restrictCharacters_comp (f : F ⟶ G) (g : G ⟶ H) :
    DualityPairing.restrictCharacters (f ≫ g) = DualityPairing.restrictCharacters g ≫ DualityPairing.restrictCharacters f := by
  ext T χ
  rfl

theorem characters_retraction (i : F ⟶ G) (r : G ⟶ F) (h : i ≫ r = 𝟙 F) :
    DualityPairing.restrictCharacters r ≫ DualityPairing.restrictCharacters i = 𝟙 (DualityPairing.cartierCharacters F) := by
  rw [← restrictCharacters_comp, h, restrictCharacters_id]

def characterBlockIso
    (A : (Over S)ᵒᵖ ⥤ Type 1)
    (e : A ≅ DualityPairing.cartierCharacters G)
    (B : (Over S)ᵒᵖ ⥤ Type 1) (iB : B ⟶ A) (rB : A ⟶ B)
    (hB : iB ≫ rB = 𝟙 B) (i : F ⟶ G) (r : G ⟶ F) (h : i ≫ r = 𝟙 F)
    (hadj : (rB ≫ iB) ≫ e.hom = e.hom ≫ DualityPairing.restrictCharacters (r ≫ i)) :
    B ≅ DualityPairing.cartierCharacters F := by
  have hp : (rB ≫ iB) ≫ e.hom =
      e.hom ≫ (DualityPairing.restrictCharacters i ≫ DualityPairing.restrictCharacters r) := by
    rw [← restrictCharacters_comp]
    exact hadj
  exact RetractIso.isoOfCompatibleRetracts e iB rB (DualityPairing.restrictCharacters r) (DualityPairing.restrictCharacters i)
    hB (characters_retraction i r h) hp

theorem characterBlockIso_hom
    (A : (Over S)ᵒᵖ ⥤ Type 1) (e : A ≅ DualityPairing.cartierCharacters G)
    (B : (Over S)ᵒᵖ ⥤ Type 1) (iB : B ⟶ A) (rB : A ⟶ B)
    (hB : iB ≫ rB = 𝟙 B) (i : F ⟶ G) (r : G ⟶ F) (h : i ≫ r = 𝟙 F)
    (hadj : (rB ≫ iB) ≫ e.hom = e.hom ≫ DualityPairing.restrictCharacters (r ≫ i)) :
    (characterBlockIso A e B iB rB hB i r h hadj).hom = iB ≫ e.hom ≫ DualityPairing.restrictCharacters i := rfl

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.CharacterRetracts
