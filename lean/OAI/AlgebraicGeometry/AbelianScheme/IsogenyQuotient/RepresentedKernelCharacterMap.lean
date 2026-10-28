import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardMonomorphism
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupMaps

/-! # Represented Kernel Character Map -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RepresentedKernelCharacterMap.Construction

noncomputable section

/-! A universal kernel character gives an actual morphism to the
Cartier representative, with a Picard recovery formula on every test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardMonomorphism.Construction.KernelCharacters

universe u
variable {S : Scheme.{u}} {A B K : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f]
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (Y : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
  (j : uliftYoneda.{u + 1}.obj K ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)
  (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (op K))
  (hχ : CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f K χ = j.app (op K) (ULift.up (𝟙 K)))

def representedKernelCharacterMap : K ⟶ Y.dual.X := (Y.sectionEquiv K).symm χ

include hχ in
theorem representedKernelCharacterMap_value {T : Over S} (x : T ⟶ K) :
    CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T (Y.sectionEquiv T (x ≫ representedKernelCharacterMap f Y χ)) =
      j.app (op T) (ULift.up x) := by
  rw [Y.sectionEquiv_natural, representedKernelCharacterMap, MulEquiv.apply_symm_apply]
  have hn := (CartierDuality.PicardMonomorphism.Construction.KernelCharacters.characterToPicardTypeSheafMap f).hom.naturality_apply x.op χ
  change CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T ((CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map x.op χ) =
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.map x.op (CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f K χ) at hn
  rw [hχ] at hn
  have hj := (congrArg (fun t : (uliftYoneda.{u + 1}.obj K).obj (op K) ⟶
      (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T) => t (ULift.up (𝟙 K))) (j.naturality x.op)).symm
  change (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.map x.op (j.app (op K) (ULift.up (𝟙 K))) =
    j.app (op T) (ULift.up (x ≫ 𝟙 K)) at hj
  rw [Category.comp_id] at hj
  exact hn.trans hj

include hχ in
theorem representedKernelCharacterMap_mono [Mono j] : Mono (representedKernelCharacterMap f Y χ) := by
  constructor
  intro T x y hxy
  have hm : Mono (j.app (op T)) := inferInstance
  apply ULift.up_injective
  apply (CategoryTheory.mono_iff_injective _).mp hm
  exact (representedKernelCharacterMap_value f Y j χ hχ x).symm.trans
    ((congrArg (fun a => CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T (Y.sectionEquiv T a)) hxy).trans
      (representedKernelCharacterMap_value f Y j χ hχ y))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RepresentedKernelCharacterMap.Construction
