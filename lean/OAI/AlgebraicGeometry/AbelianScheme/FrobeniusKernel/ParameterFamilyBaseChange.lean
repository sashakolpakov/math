import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterFamily

/-! # Parameter Family Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterFamilyBaseChange.Construction

noncomputable section

/-! The actual parameter-family map commutes with the canonical
comparison between iterated and single source base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterFamily.Construction.KernelCharacters

variable {S S' : Scheme} (s : S' ⟶ S) (Q : Over S') (B : Over S)

theorem parameterFamilyMap_baseChange :
    CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap ((Over.pullback s).obj B) Q ≫ (ParameterBaseChange.Construction.parameterBaseChangeInv s Q B).left =
      (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso B s Q).hom ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B ((Over.map s).obj Q) := by
  apply pullback.hom_ext
  · have hp : (ParameterBaseChange.Construction.parameterBaseChangeInv s Q B).left ≫
        pullback.fst B.hom ((Over.map s).obj Q).hom =
        pullback.fst ((Over.pullback s).obj B).hom Q.hom ≫ pullback.fst B.hom s :=
      ParameterBaseChange.Construction.parameterBaseChangeInv_projection s Q B
    rw [Category.assoc, hp,
      ← Category.assoc, CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_fst,
      Category.assoc, CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_fst]
    exact (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso_hom_snd B s Q).symm
  · have h : (ParameterBaseChange.Construction.parameterBaseChangeInv s Q B).left ≫ pullback.snd B.hom ((Over.map s).obj Q).hom =
        pullback.snd ((Over.pullback s).obj B).hom Q.hom :=
      (ParameterBaseChange.Construction.parameterBaseChangeInv s Q B).w
    rw [Category.assoc, h, CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_snd,
      Category.assoc, CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_snd]
    exact (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso_hom_fst B s Q).symm

theorem parameterFamilyMap_baseChange_inv :
    (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso B s Q).inv ≫
        CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap ((Over.pullback s).obj B) Q ≫ (ParameterBaseChange.Construction.parameterBaseChangeInv s Q B).left =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B ((Over.map s).obj Q) := by
  rw [parameterFamilyMap_baseChange, Iso.inv_hom_id_assoc]

theorem parameterLineClass_baseChange
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((Over.pullback ((Over.map s).obj Q).hom).obj B).left) :
    (AbelianModuli.HilbertConstruction.Picard.BaseChange.relativePicardPresheafBaseChangeIso B s).hom.app (.op Q)
      (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass ((Over.pullback s).obj B) Q
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (ParameterBaseChange.Construction.parameterBaseChangeInv s Q B).left L)) =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B ((Over.map s).obj Q) L := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso B s Q).inv
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap ((Over.pullback s).obj B) Q)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (ParameterBaseChange.Construction.parameterBaseChangeInv s Q B).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))) = _
  exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso B s Q).inv
      (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap ((Over.pullback s).obj B) Q)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (ParameterBaseChange.Construction.parameterBaseChangeInv s Q B).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))).symm.trans
    ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp
      ((AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso B s Q).inv ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap ((Over.pullback s).obj B) Q)
      (ParameterBaseChange.Construction.parameterBaseChangeInv s Q B).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)).symm.trans
      (congrArg (fun t => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass t (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))
        ((Category.assoc _ _ _).trans (parameterFamilyMap_baseChange_inv s Q B))))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterFamilyBaseChange.Construction
