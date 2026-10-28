import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CartierPicardSheafPoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicationCharacterSheaf
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.KernelSections
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.WeilPairing

/-! # Weil Character Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.WeilCharacterDescent

noncomputable section

/-! The actual CartierDuality Weil character is recovered from a line's Picard
point, using the proved Cartier-to-Picard isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace Construction

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.WeilPairing.Construction.KernelCharacters

universe u

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (ell : A ⟶ D.withPicardGroup.abelian) [IsMonHom ell]
  [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
  (n : ℕ) (hn : 0 < n)
  [IsFinite ((𝟙 A) ^ n).left] [Flat ((𝟙 A) ^ n).left]
  [Surjective ((𝟙 A) ^ n).left] [LocallyOfFinitePresentation ((𝟙 A) ^ n).left]
  (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))))

theorem torsionCartierPicardIso_character_inclusion (Q : Over S)
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)))).obj.obj (.op Q)) :
    (kernel.ι (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk D.withPicardGroup.abelian)) n)).hom.app (.op Q)
      ((CartierDuality.WeilPairing.Construction.KernelCharacters.torsionCartierPicardIso A D ell n hn C).hom.hom.app (.op Q)
        (MultiplicationCharacterSheaf.Construction.multiplicationCharacterToTorsionSheaf A n Q χ)) =
      ULift.up (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint ((𝟙 A) ^ n) Q χ D.withPicardGroup) := by
  let e := (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).mapIso (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).op
  let j := CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf ((𝟙 A) ^ n) D.withPicardGroup C n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n)
  have he : e.inv ≫ (CartierDuality.WeilPairing.Construction.KernelCharacters.torsionCartierPicardIso A D ell n hn C).hom = j := e.inv_hom_id_assoc j
  have hv := congrArg (fun a =>
    (kernel.ι (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk D.withPicardGroup.abelian)) n)).hom.app (.op Q)
      (a.hom.app (.op Q) (CartierDuality.SheafCharacterComparison.Construction.Schemes.representedCharacterSectionsMulEquiv S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))) Q χ))) he
  exact hv.trans (CartierPicardSheafPoints.Construction.cartierToPicardTorsionSheaf_character_inclusion ((𝟙 A) ^ n) D.withPicardGroup C n
    (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) Q χ)

theorem weilPairing_value_of_character_line (Q : Over S)
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)))).obj.obj (.op Q))
    (y : (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk D.withPicardGroup.abelian)) n).obj.obj (.op Q))
    (hy : (kernel.ι (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk D.withPicardGroup.abelian)) n)).hom.app (.op Q) y =
      ULift.up (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint ((𝟙 A) ^ n) Q χ D.withPicardGroup))
    (x : Q ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)) :
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) n) Q
      ((CartierDuality.WeilPairing.Construction.KernelCharacters.weilPairing A D ell n hn C).rightAdjoint.hom.app (.op Q) y)
      ((CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).hom.hom.app (.op Q) (ULift.up x)) =
        ULift.up (CartierDuality.Evaluation.Construction.CharacterEvaluation.value χ x) := by
  let e := CartierDuality.WeilPairing.Construction.KernelCharacters.torsionCartierPicardIso A D ell n hn C
  let a := MultiplicationCharacterSheaf.Construction.multiplicationCharacterToTorsionSheaf A n Q χ
  have hy' : e.hom.hom.app (.op Q) a = y := by
    apply (Sheaf.KernelSections.Construction.sheafKernelSectionsEquiv
      (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk D.withPicardGroup.abelian)) n) Q).injective
    apply Subtype.ext
    exact (Sheaf.KernelSections.Construction.sheafKernelSectionsEquiv_val _ Q _).trans
      ((torsionCartierPicardIso_character_inclusion A D ell n hn C Q χ).trans
        (hy.symm.trans (Sheaf.KernelSections.Construction.sheafKernelSectionsEquiv_val _ Q y).symm))
  have hr : e.inv.hom.app (.op Q) y = a :=
    (congrArg (fun b => e.inv.hom.app (.op Q) b) hy'.symm).trans
      (congrArg (fun b => b.hom.app (.op Q) a) e.hom_inv_id)
  rw [CartierDuality.WeilPairing.Construction.KernelCharacters.weilPairing_rightAdjoint]
  exact (congrArg (fun b => CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) n) Q b
    ((CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).hom.hom.app (.op Q) (ULift.up x))) hr).trans
      (MultiplicationCharacterSheaf.Construction.multiplicationCharacterToTorsionSheaf_value A n Q χ x)

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.WeilCharacterDescent
