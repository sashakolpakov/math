import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardHomomorphism
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafCharacterComparison

/-! # Picard Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardSheaf

noncomputable section

/-!
# CartierDuality: actual Cartier character descent as a morphism of commutative fppf sheaves
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.KernelCharacters

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A]
    (f : A ⟶ B) [IsMonHom f]
    [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
    (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) (C : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
    (n : ℕ) (hn : ∀ (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1)

/-- The character-line morphism in the actual commutative fppf-sheaf category. -/
def cartierToPicardTorsionSheaf :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    letI : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
    CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))) ⟶
      TorsionSheaves.Construction.Schemes.torsionFppfAb (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk D.abelian)) n :=
  letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  letI : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
  letI : IsCommMonObj C.dual.X := C.commutative
  C.representedCartierDualIso.inv ≫
    RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup f D C n hn) ≫
      (TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk D.abelian) n).hom

/-- The sheaf map agrees with the constructed native torsion homomorphism under the canonical representations. -/
theorem cartierToPicardTorsionSheaf_representation :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    letI : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
    letI : IsCommMonObj C.dual.X := C.commutative
    C.representedCartierDualIso.hom ≫ cartierToPicardTorsionSheaf f D C n hn =
      RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup f D C n hn) ≫
        (TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk D.abelian) n).hom := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  have : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
  have : IsCommMonObj C.dual.X := C.commutative
  exact C.representedCartierDualIso.hom_inv_id_assoc _

/-- Native perfection transfers to the actual Cartier and torsion sheaves through the canonical representations. -/
theorem cartierToPicardTorsionSheaf_isIso
    (h : letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
      letI : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
      IsIso (PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup f D C n hn)) :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    letI : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
    IsIso (cartierToPicardTorsionSheaf f D C n hn) := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  have : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
  have : IsCommMonObj C.dual.X := C.commutative
  have : IsIso (PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup f D C n hn) := h
  have : IsIso (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup f D C n hn)) :=
    (SheafBaseChange.Construction.Schemes.representedFppfAbIso (asIso (PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup f D C n hn))).isIso_hom
  change IsIso (C.representedCartierDualIso.inv ≫
    RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup f D C n hn) ≫
      (TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk D.abelian) n).hom)
  infer_instance

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardSheaf
