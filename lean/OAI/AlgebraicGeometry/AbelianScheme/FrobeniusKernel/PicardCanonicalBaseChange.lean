import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierPicardBaseChange
import OAI.AlgebraicGeometry.Picard.Homomorphisms.CanonicalDualData

/-! # Picard Canonical Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCanonicalBaseChange.Construction

noncomputable section

/-! Equipping the dual with its intrinsic Picard group retains the
same represented character-line point before and after base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] BaseChange.Construction.pulledBackGroup

variable {S S' : Scheme} (s : S' ⟶ S)
variable {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
variable (f' : (Over.pullback s).obj A ⟶ (Over.pullback s).obj B) [IsMonHom f']
variable (hf : f' = (Over.pullback s).map f)
variable (C' : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S' (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f'))) (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B)

omit [IsMonHom f] in
theorem nativeCartierPicardChangedMap_canonical :
    CartierPicardBaseChange.Construction.nativeCartierPicardChangedMap s f f' hf C' D.withPicardGroup =
      letI := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_affine s f f' hf
      letI := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_flat s f f' hf
      letI := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_surjective s f f' hf
      letI := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_presentation s f f' hf
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f' (D.pullback s).withPicardGroup C' := rfl

theorem nativeCartierPicard_baseChange_canonical
    (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))) :
    letI := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_affine s f f' hf
    letI := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_flat s f f' hf
    letI := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_surjective s f f' hf
    letI := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_presentation s f f' hf
    (CartierPicardBaseChange.Construction.nativeCartierBaseChangeAlong s f f' hf C C').hom.hom ≫
        CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f' (D.pullback s).withPicardGroup C' =
      (Over.pullback s).map (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D.withPicardGroup C) := by
  exact (congrArg (fun z => (CartierPicardBaseChange.Construction.nativeCartierBaseChangeAlong s f f' hf C C').hom.hom ≫ z)
    (nativeCartierPicardChangedMap_canonical s f f' hf C' D)).symm.trans
      (CartierPicardBaseChange.Construction.nativeCartierPicard_baseChange_along s f f' hf C C' D.withPicardGroup)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCanonicalBaseChange.Construction
