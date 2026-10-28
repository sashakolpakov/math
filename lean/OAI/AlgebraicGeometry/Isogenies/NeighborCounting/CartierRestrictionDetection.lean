import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterDualSource
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardMonomorphism
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RepresentedMorphisms

/-! # Cartier Restriction Detection -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting.CartierRestrictionDetection

/-! Restriction of an actual kernel character is trivial exactly when
its descended Picard point is trivial after the original dual source
map. Character descent is a monomorphism on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardMonomorphism.Construction.KernelCharacters OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterDualSource.Construction

variable {k : Type} [Field k] {A B A' B' : Over (Spec (.of k))}
variable [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
variable [Smooth A'.hom] [IsProper A'.hom] [GeometricallyConnected A'.hom]
variable (f : A ⟶ B) (f' : A' ⟶ B') [IsMonHom f] [IsMonHom f']
variable (a : A' ⟶ A) (b : B' ⟶ B) [IsMonHom a] [IsMonHom b]
variable (h : a ≫ f = f' ≫ b)
variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
variable [IsAffineHom f'.left] [Flat f'.left] [Surjective f'.left] [LocallyOfFinitePresentation f'.left]
variable (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) (D' : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B')
variable (C : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
variable (C' : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f')))

theorem source_character_restriction_zero_iff (T : Over (Spec (.of k))) (z : T ⟶ C.dual.X) :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D'
    z ≫ (C.dualMap C' (AbelianScheme.FrobeniusKernel.ParameterCharacterSourceRestriction.Construction.kernelSourceSquareGroupMap f f' a b h)).hom.hom = 1 ↔
      z ≫ AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C ≫ Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D' D b = 1 := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D'
  have : Mono (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f' D' C') := AbelianScheme.CartierDuality.PicardMonomorphism.Construction.KernelCharacters.cartierToPicard_mono f' D' C'
  have : IsMonHom (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f' D' C') := AbelianScheme.CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicard_isMonHom f' D' C'
  have hs := AbelianScheme.FrobeniusKernel.CharacterDualSource.Construction.canonicalCartierPicardMap_source f f' a b h D D' C C'
  have he : (z ≫ (C.dualMap C' (AbelianScheme.FrobeniusKernel.ParameterCharacterSourceRestriction.Construction.kernelSourceSquareGroupMap f f' a b h)).hom.hom) ≫
      AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f' D' C' = z ≫ AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C ≫ Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D' D b :=
    (Category.assoc _ _ _).trans (congrArg (fun w => z ≫ w) hs)
  constructor
  · intro hz
    exact he.symm.trans ((congrArg (fun w => w ≫ AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f' D' C') hz).trans
      (MonObj.one_comp _))
  · intro hz
    apply (cancel_mono (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f' D' C')).mp
    exact (he.trans hz).trans (MonObj.one_comp _).symm

end AlgebraicGeometry.Isogenies.NeighborCounting.CartierRestrictionDetection

namespace AlgebraicGeometry.Isogenies.NeighborCounting.CartierRestrictionDetection.Sheaf

/-! Actual character descent into dual torsion detects zero sections
on all test schemes, including nonreduced schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardMonomorphism.Construction.KernelCharacters OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes

variable {k : Type} [Field k] {A B : Over (Spec (.of k))}
variable [GrpObj A] [GrpObj B] [IsCommMonObj A]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
variable (f : A ⟶ B) [IsMonHom f]
variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
variable (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B)
variable (C : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
variable (n : ℕ) (hn : ∀ (T : Over (Spec (.of k))) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1)

theorem cartierTorsionSheaf_mono :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    letI : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
    Mono (AbelianScheme.CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf f D C n hn) := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  have : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
  have : IsCommMonObj C.dual.X := C.commutative
  have : Mono (AbelianScheme.CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup f D C n hn).hom.hom :=
    AbelianScheme.CartierDuality.PicardMonomorphism.Construction.KernelCharacters.cartierToPicardTorsion_mono f D C n hn
  have : Mono (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (AbelianScheme.CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup f D C n hn)) :=
    AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_mono (AbelianScheme.CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup f D C n hn)
  change Mono (C.representedCartierDualIso.inv ≫
    AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (AbelianScheme.CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup f D C n hn) ≫
      (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk D.abelian) n).hom)
  infer_instance

theorem cartierTorsionSheaf_zero_iff (T : Over (Spec (.of k)))
    (z : (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))).obj.obj (.op T)) :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    letI : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
    (AbelianScheme.CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf f D C n hn).hom.app (.op T) z = 1 ↔ z = 1 := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  have : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
  have : Mono (AbelianScheme.CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf f D C n hn) := cartierTorsionSheaf_mono f D C n hn
  let p := (AbelianScheme.CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf f D C n hn).hom.app (.op T)
  have hp : Function.Injective p := (CommGrpCat.mono_iff_injective p).mp inferInstance
  constructor
  · intro h
    exact hp (h.trans p.hom.map_one.symm)
  · intro h
    exact (congrArg p h).trans p.hom.map_one

end AlgebraicGeometry.Isogenies.NeighborCounting.CartierRestrictionDetection.Sheaf

end

end OAI
