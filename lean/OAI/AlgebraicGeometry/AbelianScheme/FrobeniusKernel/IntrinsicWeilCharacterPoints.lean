import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SheafPairingCharacterPoints
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.WeilPairing

/-! # Intrinsic Weil Character Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicWeilCharacterPoints

noncomputable section

section

/-! The canonical Weil pairing on a point represented by a descended
Cartier character is the original character evaluation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom
attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative

namespace Construction

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.WeilPairing.Construction.KernelCharacters

variable {S : Scheme} (A : Over S) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (ell : A ⟶ D.withPicardGroup.abelian) [IsMonHom ell]
    [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
    (n : ℕ) (hn : 0 < n)
    [IsFinite ((𝟙 A : A ⟶ A) ^ n).left] [Flat ((𝟙 A : A ⟶ A) ^ n).left]
    [Surjective ((𝟙 A : A ⟶ A) ^ n).left] [LocallyOfFinitePresentation ((𝟙 A : A ⟶ A) ^ n).left]
    (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))))

local instance nativeWeilPoint_cartier_comm : IsCommMonObj C.dual.X := C.commutative

theorem nativeTorsionCartierIso_representation :
    C.representedCartierDualIso.hom ≫
        (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).inv.op ≫
        (CartierDuality.WeilPairing.Construction.KernelCharacters.torsionCartierPicardIso A D ell n hn C).hom =
      CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup ((𝟙 A) ^ n)
        D.withPicardGroup C n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n)) ≫
        (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk D.withPicardGroup.abelian) n).hom := by
  let e := (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).mapIso (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).op
  have he : C.representedCartierDualIso.hom ≫ e.inv ≫ e.hom ≫
      CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf ((𝟙 A) ^ n) D.withPicardGroup C n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) =
      C.representedCartierDualIso.hom ≫
        CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf ((𝟙 A) ^ n) D.withPicardGroup C n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) := by
    exact congrArg (fun z => C.representedCartierDualIso.hom ≫ z)
      (e.inv_hom_id_assoc (CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf ((𝟙 A) ^ n)
        D.withPicardGroup C n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n)))
  exact he.trans (CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf_representation ((𝟙 A) ^ n)
    D.withPicardGroup C n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n))

theorem nativeWeilPairing_characterPoint (T : Over S) (d : T ⟶ C.dual.X)
    (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)) :
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) n) T
      ((CartierDuality.WeilPairing.Construction.KernelCharacters.weilPairing A D ell n hn C).rightAdjoint.hom.app (.op T)
        ((CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk D.withPicardGroup.abelian) n).hom.hom.app (.op T)
          (ULift.up (d ≫ CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion ((𝟙 A) ^ n) D.withPicardGroup n
            (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) C))))
      ((CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).hom.hom.app (.op T) (ULift.up x)) =
      ULift.up (C.evaluationValue T d x) := by
  rw [CartierDuality.WeilPairing.Construction.KernelCharacters.weilPairing_rightAdjoint]
  exact (SheafPairingCharacterPoints.Construction.sheafPairing_characterPoint (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n)
    C.representedCartierDualIso (CartierDuality.WeilPairing.Construction.KernelCharacters.torsionCartierPicardIso A D ell n hn C)
    (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup ((𝟙 A) ^ n)
      D.withPicardGroup C n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n)) ≫
      (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk D.withPicardGroup.abelian) n).hom)
    (nativeTorsionCartierIso_representation A D ell n hn C) T (ULift.up d) (ULift.up x)).trans
    (C.representedCartierDualIso_value T d x)

include ell hn in
theorem nativeCartierTorsion_surjective_points (T : Over S)
    (y : T ⟶ TorsionQuotient.SubgroupFunctor.torsionScheme D.withPicardGroup.abelian n) :
    ∃ d : T ⟶ C.dual.X,
      d ≫ CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion ((𝟙 A) ^ n) D.withPicardGroup n
        (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) C = y := by
  let c := CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup ((𝟙 A) ^ n) D.withPicardGroup C n
    (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n)
  have : IsIso c := CartierDuality.RelativeIso.Construction.KernelCharacters.relativeMultiplicationCartierToPicardTorsionGroup_isIso A D ell n hn C
  let e := (Grp.forget (Over S)).mapIso (asIso c)
  exact ⟨y ≫ e.inv, (Category.assoc _ _ _).trans
    ((congrArg (fun z => y ≫ z) e.inv_hom_id).trans (Category.comp_id _))⟩

theorem nativeWeilPairing_of_characterPoint (T : Over S) (d : T ⟶ C.dual.X)
    (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))
    (y : T ⟶ TorsionQuotient.SubgroupFunctor.torsionScheme D.withPicardGroup.abelian n)
    (hy : d ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard ((𝟙 A) ^ n) D.withPicardGroup C =
      y ≫ TorsionQuotient.SubgroupFunctor.torsionι D.withPicardGroup.abelian n) :
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) n) T
      ((CartierDuality.WeilPairing.Construction.KernelCharacters.weilPairing A D ell n hn C).rightAdjoint.hom.app (.op T)
        ((CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk D.withPicardGroup.abelian) n).hom.hom.app (.op T)
          (ULift.up y)))
      ((CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).hom.hom.app (.op T) (ULift.up x)) =
      ULift.up (C.evaluationValue T d x) := by
  have : Mono (TorsionQuotient.SubgroupFunctor.torsionι D.withPicardGroup.abelian n) :=
    inferInstanceAs (Mono (CategoryTheory.Limits.equalizer.ι ((𝟙 D.withPicardGroup.abelian) ^ n) 1))
  have he : d ≫ CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion ((𝟙 A) ^ n) D.withPicardGroup n
      (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) C = y := by
    apply (cancel_mono (TorsionQuotient.SubgroupFunctor.torsionι D.withPicardGroup.abelian n)).mp
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z => d ≫ z) (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion_inclusion ((𝟙 A) ^ n)
        D.withPicardGroup n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) C)).trans hy)
  exact (congrArg (fun z => CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue
      (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) n) T
      ((CartierDuality.WeilPairing.Construction.KernelCharacters.weilPairing A D ell n hn C).rightAdjoint.hom.app (.op T)
        ((CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk D.withPicardGroup.abelian) n).hom.hom.app (.op T)
          (ULift.up z)))
      ((CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).hom.hom.app (.op T) (ULift.up x))) he).symm.trans
    (nativeWeilPairing_characterPoint A D ell n hn C T d x)

end Construction

end

/-! The actual CartierDuality Weil value on native torsion points, retaining the
original morphism to the multiplicative group rather than its universe lift. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom
attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative

namespace Construction

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.WeilPairing.Construction.KernelCharacters

variable {S : Scheme} (A : Over S) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (ell : A ⟶ D.withPicardGroup.abelian) [IsMonHom ell]
    [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
    (n : ℕ) (hn : 0 < n)
    [IsFinite ((𝟙 A : A ⟶ A) ^ n).left] [Flat ((𝟙 A : A ⟶ A) ^ n).left]
    [Surjective ((𝟙 A : A ⟶ A) ^ n).left] [LocallyOfFinitePresentation ((𝟙 A : A ⟶ A) ^ n).left]
    (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))))

def nativeWeilPointValue (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))
    (y : T ⟶ TorsionQuotient.SubgroupFunctor.torsionScheme D.withPicardGroup.abelian n) :
    T ⟶ (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X :=
  (CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) n) T
    ((CartierDuality.WeilPairing.Construction.KernelCharacters.weilPairing A D ell n hn C).rightAdjoint.hom.app (.op T)
      ((CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk D.withPicardGroup.abelian) n).hom.hom.app (.op T)
        (ULift.up y)))
    ((CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).hom.hom.app (.op T) (ULift.up x))).down

theorem nativeWeilPointValue_of_character (T : Over S) (d : T ⟶ C.dual.X)
    (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))
    (y : T ⟶ TorsionQuotient.SubgroupFunctor.torsionScheme D.withPicardGroup.abelian n)
    (hy : d ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard ((𝟙 A) ^ n) D.withPicardGroup C =
      y ≫ TorsionQuotient.SubgroupFunctor.torsionι D.withPicardGroup.abelian n) :
    nativeWeilPointValue A D ell n hn C T x y = C.evaluationValue T d x :=
  congrArg ULift.down (nativeWeilPairing_of_characterPoint A D ell n hn C T d x y hy)

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicWeilCharacterPoints
