import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.CharacterPullback
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.PullbackSquare

/-! # Line Pullback Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.LinePullbackKernel.Construction

noncomputable section

/-! Original pullback-trivial lines and parameterized character lines
have the same actual trivial pullback after every parameter change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B)

theorem originalLineParameter_pullback_trivial (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left)
    (hL : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left)
    (Q : Over S) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback Q.hom).map f).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (pullback.fst B.hom Q.hom))) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass ((Over.pullback Q.hom).obj A).left := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback Q.hom).map f).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (pullback.fst B.hom Q.hom) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) = _
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp,
    ← (CartierDuality.LocalIsomorphismsIs.Construction.LocalIsomorphisms.pullbackMap_isPullback Q.hom f).w,
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, hL, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial]

theorem originalLineParameter_class_natural (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left)
    {P Q : Over S} (t : P ⟶ Q) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B t)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (pullback.fst B.hom Q.hom))) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (pullback.fst B.hom P.hom)) := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B t)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (pullback.fst B.hom Q.hom) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) = _
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap_fst]
  rfl

theorem parameterCharacterLine_actual_pullback_trivial
    [GrpObj A] [GrpObj B] [IsMonHom f]
    [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
    (Q : Over S) (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q)) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback Q.hom).map f).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass ((Over.pullback Q.hom).obj A).left := by
  have ha : IsAffineHom ((Over.pullback Q.hom).map f).left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).1
  have hf : Flat ((Over.pullback Q.hom).map f).left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.1
  have hs : Surjective ((Over.pullback Q.hom).map f).left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.2
  exact (CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterPullbackKernelClass ((Over.pullback Q.hom).map f)
    (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ) (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q χ)).property

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.LinePullbackKernel.Construction
