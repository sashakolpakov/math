import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FamilyCharacterLineCover
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Product.LineKernelCharacter

/-! # Family Picard Kernel Cover -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FamilyPicardKernelCover.Construction

noncomputable section

/-! An actual pullback-trivial product-family line recovers a section
of the original kernel character sheaf on an etale cover, with its
precise value in the original homogeneous Picard sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
  [IsProper B.hom] [Smooth B.hom] [GeometricallyConnected B.hom]
  (f : A ⟶ B) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))

include C in
set_option backward.isDefEq.respectTransparency false in
theorem exists_familyPicardKernelCharacter_cover
    {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k))
    (n : ℕ) (hn : 0 < n) (hk : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1)
    (T : Over S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ B).left)
    (hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback ((𝟙 T) ⊗ₘ f).left) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (T ⊗ A).left)
    (y : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T))
    (hy : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (op T) y) :
    ∃ (P : Over S) (a : P ⟶ T), Etale a.left ∧ Surjective a.left ∧
      ∃ χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (op P),
        CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f P χ = (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.map a.op y := by
  let N := Parameter.FamilyLineTransport.Construction.productFamilyParameterLine T L
  obtain ⟨P, a, ha, hs, χ, hχ⟩ := FamilyCharacterLineCover.Construction.exists_familyCharacterLine_cover f T N
    (Parameter.FamilyLineTransport.Construction.productFamilyParameterLine_pullback_trivial f T L hc) C p n hn hk
  refine ⟨P, a, ha, hs, χ, ?_⟩
  have hm : Mono ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (op P)) := inferInstance
  apply (CategoryTheory.mono_iff_injective _).mp hm
  have hclass : CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B P (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f P χ) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B).map a.op (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) :=
    (congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B P)) hχ.symm).trans
      ((Parameter.LineComposition.Construction.parameterLineClass_restrict B a N).symm.trans
        (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B).map a.op) (Parameter.FamilyLineTransport.Construction.productFamilyParameterLine_class T L)))
  exact (Kernel.CharacterPicardValue.Construction.kernelCharacterPicardHom_relative_value f P χ).trans
    ((congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (op P)) hclass).trans
      (((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).naturality_apply a.op (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)).trans
        ((congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf B).obj.map a.op) hy).trans
          ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.naturality_apply a.op y).symm)))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FamilyPicardKernelCover.Construction
