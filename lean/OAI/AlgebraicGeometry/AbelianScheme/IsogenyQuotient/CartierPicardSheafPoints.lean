import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardSheaf
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafTorsionMaps
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RepresentedCharacterSections

/-! # Cartier Picard Sheaf Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CartierPicardSheafPoints

noncomputable section

/-! CartierDuality's Cartier-to-Picard sheaf morphism has the same actual dual
point as the parameterized line construction, after the torsion inclusion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace Construction

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardSheaf.Construction.KernelCharacters

universe u

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A]
  (f : A ⟶ B) [IsMonHom f]
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
  (n : ℕ) (hn : ∀ (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1)

set_option backward.isDefEq.respectTransparency false in
theorem cartierToPicardTorsionSheaf_point_inclusion (Q : Over S) (d : Q ⟶ C.dual.X) :
    let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    let : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
    (kernel.ι (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk D.abelian)) n)).hom.app (.op Q)
      ((CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf f D C n hn).hom.app (.op Q)
        (C.representedCartierDualIso.hom.hom.app (.op Q) (ULift.up d))) =
      ULift.up (d ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C) := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  let : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
  let : IsCommMonObj C.dual.X := C.commutative
  have hr : C.representedCartierDualIso.hom ≫ CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf f D C n hn ≫
      kernel.ι (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk D.abelian)) n) =
        CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup f D C n hn) ≫
          CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionInclusion (Grp.mk D.abelian) n) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ kernel.ι (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk D.abelian)) n))
        (CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf_representation f D C n hn)).trans
          ((Category.assoc _ _ _).trans (congrArg (fun a =>
            CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup f D C n hn) ≫ a)
              (CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionSheafIso_inclusion (Grp.mk D.abelian) n))))
  have h := congrArg (fun a => a.hom.app (.op Q) (ULift.up d)) hr
  change _ = ULift.up ((d ≫ (CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup f D C n hn).hom.hom) ≫ TorsionQuotient.SubgroupFunctor.torsionι D.abelian n) at h
  exact h.trans (congrArg ULift.up ((Category.assoc _ _ _).trans
    (congrArg (fun a => d ≫ a) (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion_inclusion f D n hn C))))

set_option backward.isDefEq.respectTransparency false in
theorem cartierToPicardTorsionSheaf_character_inclusion (Q : Over S)
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q)) :
    let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    let : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
    (kernel.ι (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk D.abelian)) n)).hom.app (.op Q)
      ((CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf f D C n hn).hom.app (.op Q)
        (CartierDuality.SheafCharacterComparison.Construction.Schemes.representedCharacterSectionsMulEquiv S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) Q χ)) =
      ULift.up (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f Q χ D) := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  let : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
  let d := (C.sectionEquiv Q).symm χ
  have hd := RepresentedCharacterSections.Construction.representedCartierDualIso_chosen_section C Q χ
  have hc := congrArg (fun a =>
    (kernel.ι (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk D.abelian)) n)).hom.app (.op Q)
      ((CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf f D C n hn).hom.app (.op Q) a)) hd.symm
  exact hc.trans ((cartierToPicardTorsionSheaf_point_inclusion f D C n hn Q d).trans
    (congrArg ULift.up ((CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicard_apply f D C Q d).trans
      (congrArg (fun a => CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f Q a D) ((C.sectionEquiv Q).apply_symm_apply χ)))))

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CartierPicardSheafPoints
