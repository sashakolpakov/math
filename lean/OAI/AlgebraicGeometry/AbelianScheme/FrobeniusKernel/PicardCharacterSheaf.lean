import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Picard
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Picard Character Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCharacterSheaf.Construction

noncomputable section

/-! Character recovery identifies the sheafified raw Picard kernel with
the actual Cartier-character sheaf on the entire fppf site. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {k : Type u} [Field k]
variable {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
variable (f : A ⟶ B) [IsMonHom f]
variable [IsFinite f.left] [Flat f.left] [Surjective f.left]
  [LocallyOfFinitePresentation f.left]

theorem characterToRawPicardKernel_sheafify_isIso :
    IsIso ((presheafToSheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type (u + 1))).map
      (Picard.Construction.characterToRawPicardKernel f)) := by
  apply ((Scheme.fppfTopology.over (Spec (.of k))).W_iff _).mp
  exact ((Scheme.fppfTopology.over (Spec (.of k))).W_iff_isLocallyBijective _).mpr
    ⟨Picard.Construction.characterToRawPicardKernel_locallyInjective f, Picard.Construction.characterToRawPicardKernel_locallySurjective f⟩

def characterToRawPicardKernelSheaf : CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) ⟶
    (presheafToSheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type (u + 1))).obj (Picard.Construction.rawPicardKernel f) :=
  ⟨Picard.Construction.characterToRawPicardKernel f ≫
    toSheafify (Scheme.fppfTopology.over (Spec (.of k))) (Picard.Construction.rawPicardKernel f)⟩

theorem characterToRawPicardKernelSheaf_isIso : IsIso (characterToRawPicardKernelSheaf f) := by
  let J := Scheme.fppfTopology.over (Spec (.of k))
  have hs : IsIso ((presheafToSheaf J (Type (u + 1))).map (Picard.Construction.characterToRawPicardKernel f)) :=
    characterToRawPicardKernel_sheafify_isIso f
  have hu : IsIso (toSheafify J (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj) :=
    isIso_toSheafify J (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).property
  have hm : IsIso (sheafifyMap J (Picard.Construction.characterToRawPicardKernel f)) :=
    inferInstanceAs (IsIso ((sheafToPresheaf J (Type (u + 1))).map
      ((presheafToSheaf J (Type (u + 1))).map (Picard.Construction.characterToRawPicardKernel f))))
  apply (isIso_iff_of_reflects_iso _ (sheafToPresheaf J (Type (u + 1)))).mp
  change IsIso (Picard.Construction.characterToRawPicardKernel f ≫ toSheafify J (Picard.Construction.rawPicardKernel f))
  rw [toSheafify_naturality]
  infer_instance

def picardKernelCharacterSheafIso : CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) ≅
    (presheafToSheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type (u + 1))).obj (Picard.Construction.rawPicardKernel f) := by
  have := characterToRawPicardKernelSheaf_isIso f
  exact asIso (characterToRawPicardKernelSheaf f)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCharacterSheaf.Construction
