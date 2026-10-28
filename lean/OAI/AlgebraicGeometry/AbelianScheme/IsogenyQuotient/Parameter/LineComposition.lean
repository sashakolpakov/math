import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.LinePullbackKernel

/-! # Line Composition -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.LineComposition.Construction

noncomputable section

/-! Parameterized line classes, their original-family coordinates,
and their pullback kernels commute with successive parameter changes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} (B : Over S)

theorem parameterPullbackMap_comp {P Q T : Over S} (a : P ⟶ Q) (b : Q ⟶ T) :
    CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B a ≫ CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B b = CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B (a ≫ b) := by
  apply pullback.hom_ext
  · rw [Category.assoc, CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap_fst, CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap_fst, CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap_fst]
  · rw [Category.assoc, CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap_snd, ← Category.assoc,
      CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap_snd, CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap_snd, Category.assoc]
    rfl

theorem parameterFamilyLine_class_natural {P Q T : Over S}
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((Over.pullback T.hom).obj B).left) (a : P ⟶ Q) (b : Q ⟶ T) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B a)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B b))) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B (a ≫ b))) := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B a)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B b) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) = _
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, parameterPullbackMap_comp]
  rfl

theorem parameterLineClass_restrict {P T : Over S} (a : P ⟶ T)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((Over.pullback T.hom).obj B).left) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B).map a.op (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B T L) =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B P (L.pullback (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B a)) := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (a ▷ B).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) = _
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_natural, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  rfl

theorem parameterFamilyLine_pullback_trivial {A : Over S} (f : A ⟶ B)
    {T Q : Over S} (a : Q ⟶ T) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((Over.pullback T.hom).obj B).left)
    (hL : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback T.hom).map f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass ((Over.pullback T.hom).obj A).left) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback Q.hom).map f).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B a))) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass ((Over.pullback Q.hom).obj A).left := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback Q.hom).map f).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B a) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) = _
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap_square f a,
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, hL, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.LineComposition.Construction
