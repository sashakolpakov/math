import OAI.AlgebraicGeometry.Picard.PoincareBundle.WeilIntrinsicCharacter
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CartierSheafPoint
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CartierTorsionRepresentative
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterSectionEvaluation

/-! # Weil Torsion Character -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.WeilTorsionCharacter

noncomputable section

/-! The standard Weil pairing at a prescribed native dual torsion point evaluates its constructed Cartier character. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

universe u

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (ell : A ⟶ D.withPicardGroup.abelian) [IsMonHom ell]
  [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
  (n : ℕ) (hn : 0 < n)
  [IsFinite ((𝟙 A : A ⟶ A) ^ n).left] [Flat ((𝟙 A : A ⟶ A) ^ n).left]
  [Surjective ((𝟙 A : A ⟶ A) ^ n).left] [LocallyOfFinitePresentation ((𝟙 A : A ⟶ A) ^ n).left]
  (C : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))))

/-- The Weil value is the represented character value at every further test scheme. -/
theorem value {Q T : Over S} (y : Q ⟶ D.withPicardGroup.abelian) (hy : y ^ n = 1)
    (a : T ⟶ Q) (b : T ⟶ Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)) :
    AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) n) T
      ((AbelianScheme.CartierDuality.WeilPairing.Construction.KernelCharacters.weilPairing A D ell n hn C).rightAdjoint.hom.app (.op T)
        ((AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk D.withPicardGroup.abelian) n).hom.hom.app (.op T)
          (ULift.up (a ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n y hy))))
      ((AbelianScheme.CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).hom.hom.app (.op T) (ULift.up b)) =
    ULift.up ((C.sectionEquiv Q (CartierTorsionRepresentative.representative A D ell n hn C y hy)).app
      (.op (Over.mk a)) b) := by
  let d := CartierTorsionRepresentative.representative A D ell n hn C y hy
  have hd : (a ≫ d) ≫ AbelianScheme.CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion ((𝟙 A) ^ n) D.withPicardGroup n
      (AbelianScheme.CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) C = a ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n y hy :=
    (Category.assoc _ _ _).trans (congrArg (fun z => a ≫ z)
      (CartierTorsionRepresentative.representative_torsion A D ell n hn C y hy))
  have hz := CartierSheafPoint.value ((𝟙 A) ^ n) D C n (AbelianScheme.CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) T (a ≫ d)
  have hz' := hz.trans (congrArg
    (fun z => (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk D.withPicardGroup.abelian) n).hom.hom.app (.op T) (ULift.up z)) hd)
  have ht := congrArg (fun z => AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) n) T
    ((AbelianScheme.CartierDuality.WeilPairing.Construction.KernelCharacters.weilPairing A D ell n hn C).rightAdjoint.hom.app (.op T) z)
    ((AbelianScheme.CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).hom.hom.app (.op T) (ULift.up b))) hz'
  exact ht.symm.trans ((WeilIntrinsicCharacter.Intrinsic.value A D ell n hn C T (a ≫ d) b).trans
    (congrArg ULift.up (CharacterSectionEvaluation.value C a d b)))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.WeilTorsionCharacter
