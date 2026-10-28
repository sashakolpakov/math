import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierRestrictionEpi
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EpiFromLift

/-! # Intrinsic Character Restriction Epi -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicCharacterRestrictionEpi.Construction

noncomputable section

/-! Local extension of actual native characters along a finite locally
free subgroup inclusion, compared with the canonical Cartier functor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {G H : Grp (Over S)} (i : H ⟶ G)

def nativeCharacterRestriction : CartierDuality.CharacterGroupSheaf.Construction.Schemes.characterCommGroupSheaf S G ⟶ CartierDuality.CharacterGroupSheaf.Construction.Schemes.characterCommGroupSheaf S H where
  hom := {
    app T := CommGrpCat.ofHom (CartierDuality.RepresentationMorphisms.Construction.Schemes.characterRestrictionHom i T.unop)
    naturality := by
      intro T U t
      apply CommGrpCat.hom_ext
      apply MonoidHom.ext
      intro χ
      exact CartierDuality.RepresentationMorphisms.Construction.Schemes.characterRestrictionHom_natural i t.unop χ }

theorem nativeCharacterRestriction_apply (T : Over S)
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (.op T)) :
    (nativeCharacterRestriction i).hom.app (.op T) χ = (CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction i).hom.app (.op T) χ := rfl

variable [IsCommMonObj G.X] [IsCommMonObj H.X]

theorem nativeCharacterRestriction_cartier :
    nativeCharacterRestriction i ≫ (CartierDuality.SheafCharacterComparison.Construction.Schemes.representedCharacterSheafIso S H).hom =
      (CartierDuality.SheafCharacterComparison.Construction.Schemes.representedCharacterSheafIso S G).hom ≫
        (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i).op := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  intro χ
  apply NatTrans.ext
  funext V
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  rintro ⟨x⟩
  rfl

theorem nativeCharacterRestriction_epi [Mono i.hom.hom]
    [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    [IsFinite H.X.hom] [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom] :
    Epi (nativeCharacterRestriction i) := by
  have : Mono (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i) := CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_mono i
  have hG : CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) :=
    ⟨G, inferInstance, inferInstance, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩
  have hH : CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S H) :=
    ⟨H, inferInstance, inferInstance, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩
  have hd : Epi ((CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i).op) :=
    CartierRestrictionEpi.Construction.cartierDualMap_epi_of_finiteLocallyFree (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i) hH hG
  exact EpiFromLift.Construction.epi_of_iso_commutative_square (CartierDuality.SheafCharacterComparison.Construction.Schemes.representedCharacterSheafIso S G)
    (CartierDuality.SheafCharacterComparison.Construction.Schemes.representedCharacterSheafIso S H) (nativeCharacterRestriction i)
      ((CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i).op) hd
        (nativeCharacterRestriction_cartier i)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicCharacterRestrictionEpi.Construction
