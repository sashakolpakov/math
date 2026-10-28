import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafCharacterComparison

/-! # Represented Character Sections -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RepresentedCharacterSections

noncomputable section

/-! Explicit native-character formulas for the existing representation
of the common-universe Cartier dual sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace Construction

universe u

variable {S : Scheme.{u}} {G : Grp (Over S)} [IsCommMonObj G.X]
  (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (Q : Over S)

theorem representedCartierDualIso_native_section (d : Q ⟶ C.dual.X) :
    C.representedCartierDualIso.hom.hom.app (.op Q) (ULift.up d) =
      CartierDuality.SheafCharacterComparison.Construction.Schemes.representedCharacterSectionsMulEquiv S G Q (C.sectionEquiv Q d) := by
  apply NatTrans.ext
  funext U
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  rintro ⟨x⟩
  rfl

theorem representedCartierDualIso_chosen_section (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (.op Q)) :
    C.representedCartierDualIso.hom.hom.app (.op Q) (ULift.up ((C.sectionEquiv Q).symm χ)) =
      CartierDuality.SheafCharacterComparison.Construction.Schemes.representedCharacterSectionsMulEquiv S G Q χ :=
  (representedCartierDualIso_native_section C Q _).trans
    (congrArg (CartierDuality.SheafCharacterComparison.Construction.Schemes.representedCharacterSectionsMulEquiv S G Q) ((C.sectionEquiv Q).apply_symm_apply χ))

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RepresentedCharacterSections
