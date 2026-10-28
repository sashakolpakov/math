import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RelativeIso
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelTorsionComparison
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafBlocks

/-! # Weil Pairing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality

noncomputable section

/-! The actual Weil pairing from descended characters and the normalized Picard dual. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

universe u

namespace WeilPairing.Construction.KernelCharacters

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (ell : A ⟶ D.withPicardGroup.abelian) [IsMonHom ell]
    [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
    (n : ℕ) (hn : 0 < n)
    [IsFinite ((𝟙 A : A ⟶ A) ^ n).left] [Flat ((𝟙 A : A ⟶ A) ^ n).left]
    [Surjective ((𝟙 A : A ⟶ A) ^ n).left] [LocallyOfFinitePresentation ((𝟙 A : A ⟶ A) ^ n).left]
    (C : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))))

/-- Actual character descent, expressed entirely in the common torsion fppf-sheaf interface. -/
def torsionCartierPicardIso :
    CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (TorsionSheaves.Construction.Schemes.torsionFppfAb (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) n) ≅
      TorsionSheaves.Construction.Schemes.torsionFppfAb (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk D.withPicardGroup.abelian)) n := by
  let j := PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf ((𝟙 A) ^ n) D.withPicardGroup C n (CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n)
  have hj : IsIso j := PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf_isIso ((𝟙 A) ^ n) D.withPicardGroup C n
    (CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n)
    (RelativeIso.Construction.KernelCharacters.relativeMultiplicationCartierToPicardTorsionGroup_isIso A D ell n hn C)
  exact (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).mapIso (KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).op ≪≫
    @asIso _ _ _ _ j hj

/-- The Weil pairing evaluates the unique character whose descended line represents the dual point. -/
def weilPairing :
    SheafEvaluation.Construction.Schemes.BilinearPairing (TorsionSheaves.Construction.Schemes.torsionFppfAb (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) n)
      (TorsionSheaves.Construction.Schemes.torsionFppfAb (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk D.withPicardGroup.abelian)) n) :=
  (SheafEvaluation.Construction.Schemes.BilinearPairing.mk (torsionCartierPicardIso A D ell n hn C).inv).flip

/-- The character in the second variable is exactly the inverse of actual character-line descent. -/
theorem weilPairing_rightAdjoint :
    (weilPairing A D ell n hn C).rightAdjoint = (torsionCartierPicardIso A D ell n hn C).inv :=
  congrArg SheafEvaluation.Construction.Schemes.BilinearPairing.leftAdjoint
    (SheafEvaluation.Construction.Schemes.BilinearPairing.flip_flip (SheafEvaluation.Construction.Schemes.BilinearPairing.mk (torsionCartierPicardIso A D ell n hn C).inv))

/-- Descent followed by the Weil character recovers the original character, on the actual sheaf. -/
theorem weilPairing_characterLine :
    (torsionCartierPicardIso A D ell n hn C).hom ≫ (weilPairing A D ell n hn C).rightAdjoint = 𝟙 _ := by
  rw [weilPairing_rightAdjoint]
  exact (torsionCartierPicardIso A D ell n hn C).hom_inv_id

/-- Cartier biduality makes both adjoints of the actual Weil pairing invertible. -/
theorem weilPairing_isPerfect
    (h : IsIso (SheafEvaluation.Construction.Schemes.sheafBidualEvaluation
      (TorsionSheaves.Construction.Schemes.torsionFppfAb (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) n))) :
    (weilPairing A D ell n hn C).IsPerfect := by
  have := h
  constructor
  · change IsIso (SheafEvaluation.Construction.Schemes.sheafBidualEvaluation _ ≫
      (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (torsionCartierPicardIso A D ell n hn C).inv.op)
    exact (@asIso _ _ _ _ (SheafEvaluation.Construction.Schemes.sheafBidualEvaluation _) h ≪≫
      (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).mapIso (torsionCartierPicardIso A D ell n hn C).symm.op).isIso_hom
  · rw [weilPairing_rightAdjoint]
    exact (torsionCartierPicardIso A D ell n hn C).isIso_inv

end WeilPairing.Construction.KernelCharacters

/-- Transporting either variable of a perfect pairing through an isomorphism preserves perfection. -/
theorem SheafEvaluation.Construction.Schemes.BilinearPairing.restrict_isPerfect_of_isIso
    {S : Scheme.{u}} {G H G' H' : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (e : SheafEvaluation.Construction.Schemes.BilinearPairing G H) (he : e.IsPerfect)
    (i : G' ⟶ G) (j : H' ⟶ H) [IsIso i] [IsIso j] : (e.restrict i j).IsPerfect := by
  have : IsIso e.leftAdjoint := he.1
  have : IsIso e.rightAdjoint := he.2
  constructor
  · change IsIso (i ≫ e.leftAdjoint ≫ (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map j.op)
    exact (asIso i ≪≫ @asIso _ _ _ _ e.leftAdjoint he.1 ≪≫
      (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).mapIso (asIso j).op).isIso_hom
  · rw [SheafEvaluation.Construction.Schemes.BilinearPairing.restrict_rightAdjoint]
    exact (asIso j ≪≫ @asIso _ _ _ _ e.rightAdjoint he.2 ≪≫
      (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).mapIso (asIso i).op).isIso_hom

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality
