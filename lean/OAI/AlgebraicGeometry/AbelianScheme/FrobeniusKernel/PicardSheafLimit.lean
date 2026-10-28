import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardLimit
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCharacterSheaf
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-! # Picard Sheaf Limit -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardSheafLimit.Construction

noncomputable section

/-! The actual Cartier character-line map is the equalizer of homogeneous
Picard pullback and the sheafified trivial map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {k : Type u} [Field k]
variable {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
variable (f : A ⟶ B) [IsMonHom f]
variable [IsFinite f.left] [Flat f.left] [Surjective f.left]
  [LocallyOfFinitePresentation f.left]

omit [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom] in
theorem characterToRawPicardKernelSheaf_inclusion :
    PicardCharacterSheaf.Construction.characterToRawPicardKernelSheaf f ≫
        (presheafToSheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type (u + 1))).map
          (Picard.Construction.rawPicardKernelInclusion f) = CartierDuality.PicardMonomorphism.Construction.KernelCharacters.characterToPicardTypeSheafMap f := by
  apply Sheaf.hom_ext
  change (Picard.Construction.characterToRawPicardKernel f ≫
      toSheafify (Scheme.fppfTopology.over (Spec (.of k))) (Picard.Construction.rawPicardKernel f)) ≫
        sheafifyMap (Scheme.fppfTopology.over (Spec (.of k))) (Picard.Construction.rawPicardKernelInclusion f) = _
  rw [Category.assoc, ← toSheafify_naturality, ← Category.assoc,
    Picard.Construction.characterToRawPicardKernel_inclusion]
  rfl

abbrev sheafifiedRawPicardKernel_isLimit :=
  isLimitForkMapOfIsLimit
    (presheafToSheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type (u + 1)))
    (PicardLimit.Construction.rawPicardKernel_condition f) (PicardLimit.Construction.rawPicardKernel_isLimit f)

omit [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom] in
theorem characterPicardKernel_condition :
    CartierDuality.PicardMonomorphism.Construction.KernelCharacters.characterToPicardTypeSheafMap f ≫ Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f =
      CartierDuality.PicardMonomorphism.Construction.KernelCharacters.characterToPicardTypeSheafMap f ≫
        (presheafToSheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type (u + 1))).map
          (PicardLimit.Construction.trivialPicardPullbackPresheaf (A := A) (B := B)) := by
  let F := presheafToSheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type (u + 1))
  have hc : F.map (Picard.Construction.rawPicardKernelInclusion f) ≫ F.map (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullbackPresheaf A B f) =
      F.map (Picard.Construction.rawPicardKernelInclusion f) ≫ F.map (PicardLimit.Construction.trivialPicardPullbackPresheaf (A := A) (B := B)) :=
    (F.map_comp _ _).symm.trans ((congrArg F.map (PicardLimit.Construction.rawPicardKernel_condition f)).trans (F.map_comp _ _))
  rw [← characterToRawPicardKernelSheaf_inclusion f]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => PicardCharacterSheaf.Construction.characterToRawPicardKernelSheaf f ≫ a) hc).trans
      (Category.assoc _ _ _).symm)

def characterPicardKernelFork : Fork (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f)
    ((presheafToSheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type (u + 1))).map
      (PicardLimit.Construction.trivialPicardPullbackPresheaf (A := A) (B := B))) :=
  Fork.ofι (CartierDuality.PicardMonomorphism.Construction.KernelCharacters.characterToPicardTypeSheafMap f) (characterPicardKernel_condition f)

def characterPicardKernel_isLimit : IsLimit (characterPicardKernelFork f) := by
  let e := PicardCharacterSheaf.Construction.picardKernelCharacterSheafIso f
  have he : e.inv ≫ CartierDuality.PicardMonomorphism.Construction.KernelCharacters.characterToPicardTypeSheafMap f =
      (presheafToSheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type (u + 1))).map
        (Picard.Construction.rawPicardKernelInclusion f) := by
    rw [← characterToRawPicardKernelSheaf_inclusion f]
    exact e.inv_hom_id_assoc _
  exact IsLimit.ofIsoLimit (sheafifiedRawPicardKernel_isLimit f)
    (Fork.ext e.symm he)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardSheafLimit.Construction
