import OAI.AlgebraicGeometry.Picard.PoincareBundle.WeilCharacterTransport
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.WeilPairing

/-! # Weil Intrinsic Character -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.WeilIntrinsicCharacter

noncomputable section

/-! The standard CartierDuality Weil pairing evaluates the actual native Cartier character. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

namespace Intrinsic

universe u

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.WeilPairing.Construction.KernelCharacters

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (ell : A ⟶ D.withPicardGroup.abelian) [IsMonHom ell]
  [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
  (n : ℕ) (hn : 0 < n)
  [IsFinite ((𝟙 A : A ⟶ A) ^ n).left] [Flat ((𝟙 A : A ⟶ A) ^ n).left]
  [Surjective ((𝟙 A : A ⟶ A) ^ n).left] [LocallyOfFinitePresentation ((𝟙 A : A ⟶ A) ^ n).left]
  (C : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))))

/-- Cartier-Picard descent followed by the Weil pairing gives the supplied character, on every test scheme. -/
theorem value (T : Over S) (d : T ⟶ C.dual.X) (x : T ⟶ Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)) :
    AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) n) T
      ((AbelianScheme.CartierDuality.WeilPairing.Construction.KernelCharacters.weilPairing A D ell n hn C).rightAdjoint.hom.app (.op T)
        ((AbelianScheme.CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf ((𝟙 A) ^ n) D.withPicardGroup C n
          (AbelianScheme.CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n)).hom.app (.op T)
          (C.representedCartierDualIso.hom.hom.app (.op T) (ULift.up d))))
      ((AbelianScheme.CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).hom.hom.app (.op T) (ULift.up x)) =
        ULift.up (C.evaluationValue T d x) := by
  have hj := AbelianScheme.CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf_isIso ((𝟙 A) ^ n) D.withPicardGroup C n
    (AbelianScheme.CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n)
    (AbelianScheme.CartierDuality.RelativeIso.Construction.KernelCharacters.relativeMultiplicationCartierToPicardTorsionGroup_isIso A D ell n hn C)
  let j := @asIso _ _ _ _
    (AbelianScheme.CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf ((𝟙 A) ^ n) D.withPicardGroup C n (AbelianScheme.CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n)) hj
  have hv := WeilCharacterTransport.value (AbelianScheme.CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n) j T
    (C.representedCartierDualIso.hom.hom.app (.op T) (ULift.up d)) (ULift.up x)
  have hr := AbelianScheme.CartierDuality.WeilPairing.Construction.KernelCharacters.weilPairing_rightAdjoint A D ell n hn C
  rw [hr]
  exact hv.trans (C.representedCartierDualIso_value T d x)

end Intrinsic

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.WeilIntrinsicCharacter
