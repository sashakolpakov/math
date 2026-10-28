import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.ParameterCharacter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.FamilyLineTransport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.CharacterPicardValue

/-! # Line Kernel Character -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Product.LineKernelCharacter.Construction

noncomputable section

/-! An actual pullback-trivial family line constructs a preimage under
the kernel-character to native Picard map, on every affine parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {k : Type u} [Field k]
  {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (f : A ⟶ B) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]

set_option backward.isDefEq.respectTransparency false in
theorem exists_kernelCharacter_of_productLine_pullback_trivial
    (T : Over (Spec (.of k))) [IsAffine T.left] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ B).left)
    (hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback ((𝟙 T) ⊗ₘ f).left) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (T ⊗ A).left)
    (y : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T))
    (hy : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (op T) y) :
    ∃ χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf _ (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (op T),
      CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T χ = y := by
  let N := Parameter.FamilyLineTransport.Construction.productFamilyParameterLine T L
  let s := Classical.choice (Quotient.exact (Parameter.FamilyLineTransport.Construction.productFamilyParameterLine_pullback_trivial f T L hc))
  let χ := Kernel.ParameterCharacter.Construction.lineParameterCharacterSection f T N s
  refine ⟨χ, ?_⟩
  have hm : Mono ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (op T)) := inferInstance
  apply (CategoryTheory.mono_iff_injective _).mp hm
  have hclass : CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B T (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f T χ) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L :=
    (Kernel.ParameterCharacter.Construction.lineParameterCharacterSection_familyClass f T N s).trans (Parameter.FamilyLineTransport.Construction.productFamilyParameterLine_class T L)
  exact (Kernel.CharacterPicardValue.Construction.kernelCharacterPicardHom_relative_value f T χ).trans
    ((congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (op T)) hclass).trans hy)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Product.LineKernelCharacter.Construction
