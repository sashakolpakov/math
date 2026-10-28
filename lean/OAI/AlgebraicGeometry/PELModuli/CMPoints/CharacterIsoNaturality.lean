import OAI.AlgebraicGeometry.PELModuli.CMPoints.CartierDualityTorsionComparison
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Intertwining

/-! # Character Iso Naturality -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.CharacterIsoNaturality

noncomputable section

/-! Naturality of the character comparisons, before specializing to
the canonical Poincare pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Intertwining.Construction

universe v
variable {S : Scheme.{0}}

theorem characterGroupCongr_natural {F G : (Over S)ᵒᵖ ⥤ GrpCat.{v}}
    (e : F ≅ G) (K : (Over S)ᵒᵖ ⥤ CommGrpCat.{v})
    (a : F ⟶ F) (b : G ⟶ G) (h : a ≫ e.hom = e.hom ≫ b) :
    AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.CommutativeSheaves.restriction a K ≫ (CartierDualityTorsionComparison.characterGroupCongr e K).hom =
      (CartierDualityTorsionComparison.characterGroupCongr e K).hom ≫ AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.CommutativeSheaves.restriction b K := by
  change AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.CommutativeSheaves.restriction a K ≫ AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.CommutativeSheaves.restriction e.inv K =
    AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.CommutativeSheaves.restriction e.inv K ≫ AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.CommutativeSheaves.restriction b K
  rw [← AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.CommutativeSheaves.restriction_comp, ← AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.CommutativeSheaves.restriction_comp,
    AbelianScheme.FrobeniusKernel.Intertwining.Construction.intertwining_inverse e a b h]

theorem uliftInternalHomIso_natural
    (F : (Over S)ᵒᵖ ⥤ GrpCat.{0}) (K : (Over S)ᵒᵖ ⥤ CommGrpCat.{0})
    (a : F ⟶ F) :
    AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.CommutativeSheaves.restriction a K ≫ (AbelianScheme.CartierDuality.SheafCharacterComparison.Construction.CommutativeSheaves.uliftInternalHomIso F K).hom =
      (AbelianScheme.CartierDuality.SheafCharacterComparison.Construction.CommutativeSheaves.uliftInternalHomIso F K).hom ≫
        AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.CommutativeSheaves.restriction (Functor.whiskerRight a GrpCat.uliftFunctor.{1, 0})
          (K ⋙ CommGrpCat.uliftFunctor.{1, 0}) := by
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  intro χ
  apply NatTrans.ext
  funext U
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  rintro ⟨x⟩
  rfl

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.CharacterIsoNaturality
