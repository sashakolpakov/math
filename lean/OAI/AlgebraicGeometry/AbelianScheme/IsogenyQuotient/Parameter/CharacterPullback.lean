import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.CharacterPicardValue
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.FamilyLineTransport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UnbundledPicardPullbackHom

/-! # Character Pullback -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.CharacterPullback.Construction

noncomputable section

/-! Parameterized Cartier character lines belong to the actual Picard
pullback kernel over every base and every parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f]
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]

omit [GrpObj A] [GrpObj B] [IsMonHom f] [IsAffineHom f.left] [Flat f.left]
    [Surjective f.left] [LocallyOfFinitePresentation f.left] in
theorem parameterLineClass_pullback (T : Over S)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((Over.pullback T.hom).obj B).left) :
    (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf f).app (op T) (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B T L) =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass A T (L.pullback ((Over.pullback T.hom).map f).left) := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T ◁ f).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap A T)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback T.hom).map f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp,
    CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_eq_symmetry, CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_eq_symmetry]
  apply congrArg (fun a => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass a (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))
  apply CategoryTheory.Limits.pullback.hom_ext <;>
    simp only [Over.whiskerLeft_left, Over.pullback_map_left, pullback.map,
      Category.assoc, pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd,
      pullback.lift_fst, pullback.lift_snd, pullbackSymmetry_hom_comp_fst_assoc,
      Category.comp_id]

omit [LocallyOfFinitePresentation f.left] in
theorem parameterCharacterLine_pullback_class (T : Over S)
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (op T)) :
    (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf f).app (op T)
      (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B T (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f T χ)) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (T ⊗ A).left := by
  rw [parameterLineClass_pullback]
  unfold CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass
  have ha : IsAffineHom ((Over.pullback T.hom).map f).left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties T.hom f).1
  have hf : Flat ((Over.pullback T.hom).map f).left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties T.hom f).2.1
  have hs : Surjective ((Over.pullback T.hom).map f).left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties T.hom f).2.2
  have hc := (CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterPullbackKernelClass ((Over.pullback T.hom).map f)
    (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f T χ) (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f T χ)).property
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback T.hom).map f).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f T χ)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass ((Over.pullback T.hom).obj A).left at hc
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap A T)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback T.hom).map f).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f T χ))) = _
  rw [hc, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial]

theorem parameterCharacterPicardHom_pullback_one (T : Over S)
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (op T)) :
    UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom f T (CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T χ) = 1 := by
  have hm : Mono ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion A).hom.app (op T)) := inferInstance
  apply (CategoryTheory.mono_iff_injective _).mp hm
  rw [UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom_apply]
  have hn := congrArg (fun p : Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B ⟶ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A =>
    p.hom.app (op T) (CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T χ))
    (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback_inclusion A B f)
  change (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion A).hom.app (op T)
    ((Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom.app (op T) (CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T χ)) = _ at hn
  rw [hn]
  change (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback f).hom.app (op T)
    ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (op T) (CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T χ)) = _
  rw [Kernel.CharacterPicardValue.Construction.kernelCharacterPicardHom_relative_value, Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback_toRelativePicard_apply,
    parameterCharacterLine_pullback_class]
  rw [← Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom_apply, map_one]
  exact Picard.Homomorphisms.RelativeGroup.Construction.trivialPicardClass_eq_one A T

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.CharacterPullback.Construction
