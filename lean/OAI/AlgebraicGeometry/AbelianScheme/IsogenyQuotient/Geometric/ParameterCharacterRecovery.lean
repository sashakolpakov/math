import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.CharacterFrameRecovery
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.FamilyLineTransport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.CharacterPicardValue
import OAI.AlgebraicGeometry.Picard.Homomorphisms.ProperGroupFunctions
import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelGeometry

/-! # Parameter Character Recovery -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.ParameterCharacterRecovery.Construction

noncomputable section

/-! Actual pullback-trivial product lines over a field-valued parameter
recover characters of the original relative kernel. The original base
is arbitrary; no Cartier representative base-change identification is needed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (f : A ⟶ B) [IsMonHom f] [IsFinite f.left] [Flat f.left] [Surjective f.left]
  [LocallyOfFinitePresentation f.left]

omit [IsMonHom f] [Surjective f.left] in
theorem fieldParameterKernel_projection_appTop_isIso
    {k : Type u} [Field k] (s : Spec (.of k) ⟶ S) :
    IsIso (fst (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f)) ((Over.pullback s).obj A)).left.appTop := by
  let A' := (Over.pullback s).obj A
  let f' := (Over.pullback s).map f
  have : Smooth A'.hom := inferInstanceAs (Smooth (pullback.snd A.hom s))
  have : IsProper A'.hom := inferInstanceAs (IsProper (pullback.snd A.hom s))
  have : GeometricallyConnected A'.hom := inferInstanceAs (GeometricallyConnected (pullback.snd A.hom s))
  have hf : IsFinite f'.left := MorphismProperty.overPullbackMap (P := @IsFinite) s _ inferInstance
  have hflat : Flat f'.left := MorphismProperty.overPullbackMap (P := @Flat) s _ inferInstance
  have hfp : LocallyOfFinitePresentation f'.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation) s _ inferInstance
  have : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme f').hom := (Picard.Homomorphisms.Kernel.Construction.kernelScheme_finiteLocallyFree f' ⟨hf, hflat, hfp⟩).1
  have : IsAffine (Picard.Homomorphisms.Kernel.Construction.kernelScheme f').left := isAffine_of_isAffineHom (Picard.Homomorphisms.Kernel.Construction.kernelScheme f').hom
  exact Picard.Homomorphisms.ProperGroupFunctions.Construction.properGroupProduct_appTop_isIso A' (Picard.Homomorphisms.Kernel.Construction.kernelScheme f')

set_option backward.isDefEq.respectTransparency false in
theorem exists_kernelCharacter_of_geometric_productLine
    {k : Type u} [Field k] (s : Spec (.of k) ⟶ S)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Over.mk s ⊗ B).left)
    (hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback ((𝟙 (Over.mk s)) ⊗ₘ f).left) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (Over.mk s ⊗ A).left)
    (y : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op (Over.mk s)))
    (hy : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (op (Over.mk s)) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (op (Over.mk s)) y) :
    ∃ χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (op (Over.mk s)),
      CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f (Over.mk s) χ = y := by
  have : IsIso (fst (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback (Over.mk s).hom).map f))
      ((Over.pullback (Over.mk s).hom).obj A)).left.appTop :=
    fieldParameterKernel_projection_appTop_isIso f s
  let N := Parameter.FamilyLineTransport.Construction.productFamilyParameterLine (Over.mk s) L
  let e := Classical.choice (Quotient.exact (Parameter.FamilyLineTransport.Construction.productFamilyParameterLine_pullback_trivial f (Over.mk s) L hc))
  obtain ⟨χ, hχ⟩ := Parameter.CharacterFrameRecovery.Construction.exists_parameterCharacter_of_pullback_frame f (Over.mk s) N e
  refine ⟨χ, ?_⟩
  have hm : Mono ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (op (Over.mk s))) := inferInstance
  apply (CategoryTheory.mono_iff_injective _).mp hm
  have hclass : CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B (Over.mk s) (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f (Over.mk s) χ) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L :=
    (congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B (Over.mk s))) hχ).trans
      (Parameter.FamilyLineTransport.Construction.productFamilyParameterLine_class (Over.mk s) L)
  exact (Kernel.CharacterPicardValue.Construction.kernelCharacterPicardHom_relative_value f (Over.mk s) χ).trans
    ((congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (op (Over.mk s))) hclass).trans hy)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.ParameterCharacterRecovery.Construction
