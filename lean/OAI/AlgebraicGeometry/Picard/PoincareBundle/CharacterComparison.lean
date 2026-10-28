import OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterFamilyFrames
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.PointNormalization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardInjection

/-! # Character Comparison -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterComparison

noncomputable section

/-! The actual CartierDuality character line is the normalized Poincare line of its represented dual point, including nonreduced parameters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace Poincare

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A.scheme)
  {X : Over (Spec (.of k))} [GrpObj X] (f : X ⟶ A.scheme) [IsMonHom f]
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (T : Over (Spec (.of k))) [CompactSpace T.left] [QuasiSeparatedSpace T.left]
  (χ : (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op T))

/-- The character construction gives an actual line isomorphism preserving the zero-section frames. -/
theorem exists_normalized_iso :
    ∃ e : (Poincare.PointNormalization.line D (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f T χ D)).sheaf ≅
        (CharacterFamilyLine.Family.line f T χ).sheaf,
      (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A.scheme)).left).map e.hom ≫
          (CharacterFamilyFrames.Family.zeroFrame f T χ).hom =
        (Poincare.PointNormalization.zeroFrame D (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f T χ D)).hom := by
  have h : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Poincare.PointNormalization.line D (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f T χ D))) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CharacterFamilyLine.Family.line f T χ)) :=
    (Poincare.PointNormalization.picardClass D (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f T χ D)).trans
      ((AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint_poincare f T χ D).trans
        (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T)) (CharacterFamilyLine.Family.line_class f T χ).symm))
  exact PELModuli.IntegralModel.NormalizedPicardInjection.NormalizedPicard.normalized_iso_of_picard_eq A
    (Poincare.PointNormalization.line D (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f T χ D))
    (CharacterFamilyLine.Family.line f T χ)
    (Poincare.PointNormalization.zeroFrame D (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f T χ D))
    (CharacterFamilyFrames.Family.zeroFrame f T χ) h

end Poincare

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterComparison
