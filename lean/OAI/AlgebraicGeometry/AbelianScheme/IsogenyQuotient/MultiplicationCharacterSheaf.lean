import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelTorsionComparison

/-! # Multiplication Character Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicationCharacterSheaf

noncomputable section

/-! A native multiplication-kernel character gives its canonical
character of the actual torsion sheaf, with unchanged evaluations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace Construction

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelTorsionComparison.Construction.Schemes

universe u

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) (Q : Over S)

def multiplicationCharacterToTorsionSheaf
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)))).obj.obj (.op Q)) :
    (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) n)).obj.obj (.op Q) :=
  ((CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).inv.op).hom.app (.op Q)
    (CartierDuality.SheafCharacterComparison.Construction.Schemes.representedCharacterSectionsMulEquiv S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))) Q χ)

theorem multiplicationCharacterToTorsionSheaf_recover
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)))).obj.obj (.op Q)) :
    ((CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).hom.op).hom.app (.op Q)
      (multiplicationCharacterToTorsionSheaf A n Q χ) =
        CartierDuality.SheafCharacterComparison.Construction.Schemes.representedCharacterSectionsMulEquiv S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))) Q χ := by
  let e := (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).mapIso (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).op
  exact congrArg (fun a => a.hom.app (.op Q)
    (CartierDuality.SheafCharacterComparison.Construction.Schemes.representedCharacterSectionsMulEquiv S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))) Q χ)) e.inv_hom_id

theorem multiplicationCharacterToTorsionSheaf_value
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)))).obj.obj (.op Q))
    (x : Q ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)) :
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) n) Q
      (multiplicationCharacterToTorsionSheaf A n Q χ)
      ((CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).hom.hom.app (.op Q) (ULift.up x)) =
        ULift.up (CartierDuality.Evaluation.Construction.CharacterEvaluation.value χ x) := by
  have h := CartierDuality.SheafEvaluation.Construction.Schemes.cartierDualSheafMap_value (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).inv Q
    (CartierDuality.SheafCharacterComparison.Construction.Schemes.representedCharacterSectionsMulEquiv S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))) Q χ)
    ((CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).hom.hom.app (.op Q) (ULift.up x))
  have hi : (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).inv.hom.app (.op Q)
      ((CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).hom.hom.app (.op Q) (ULift.up x)) = ULift.up x :=
    congrArg (fun a => a.hom.app (.op Q) (ULift.up x)) (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).hom_inv_id
  exact h.trans (congrArg (CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)))) Q
    (CartierDuality.SheafCharacterComparison.Construction.Schemes.representedCharacterSectionsMulEquiv S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))) Q χ)) hi)

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicationCharacterSheaf
