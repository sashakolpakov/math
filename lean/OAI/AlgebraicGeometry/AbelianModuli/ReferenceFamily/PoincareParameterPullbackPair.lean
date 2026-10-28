import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.KernelMorphism
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ParameterLineKernel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PairClass

/-! # Poincare Parameter Pullback Pair -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareParameterPullbackPair

noncomputable section

/-! Pulling an actual dual Poincare parameter along a scheme map
is literal Poincare evaluation. Multiplication of target maps gives
tensor multiplication in the original infinitesimal line-class kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {n : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme n Foundations.Scheme.ProjectiveSpace.complexBase) (D : HilbertConstruction.Dual.Data.DualAbelianData A)
    (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

theorem poincareParameterPullback_pair (f : X ⟶ A.scheme)
    (t : LieRanks.dualNumberTest ℂ ⟶ D.abelian.scheme) :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass D.poincare t) =
      D.poincarePairClass (LieRanks.dualNumberTest ℂ ⊗ X)
        (fst (LieRanks.dualNumberTest ℂ) X ≫ t) (snd (LieRanks.dualNumberTest ℂ) X ≫ f) := by
  have he : (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f) ≫ (t ⊗ₘ 𝟙 A.scheme) =
      lift (fst (LieRanks.dualNumberTest ℂ) X ≫ t) (snd (LieRanks.dualNumberTest ℂ) X ≫ f) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hd : D.poincarePairClass (LieRanks.dualNumberTest ℂ ⊗ X)
      (fst (LieRanks.dualNumberTest ℂ) X ≫ t) (snd (LieRanks.dualNumberTest ℂ) X ≫ f) =
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (fst (LieRanks.dualNumberTest ℂ) X ≫ t)
      (snd (LieRanks.dualNumberTest ℂ) X ≫ f)).left (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare) :=
    Quotient.sound ⟨D.poincarePairDirectIso (fst (LieRanks.dualNumberTest ℂ) X ≫ t)
      (snd (LieRanks.dualNumberTest ℂ) X ≫ f)⟩
  exact (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left
    (t ⊗ₘ 𝟙 A.scheme).left (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)).symm.trans
      ((congrArg (fun q => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass q (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))
        (congrArg Over.Hom.left he)).trans hd.symm)

theorem dualPoincareParameter_pullback_mul (f g : X ⟶ A.scheme)
    (t : DualOpen.Lifts.DualSchemePoints D.abelian.scheme 1) :
    DualLine.KernelMorphism.dualLineKernelMorphismPullback (f * g)
        (Dual.ParameterLineKernel.dualParameterLineKernel D.poincare D.normalizedAtDualZero.some t) =
      DualLine.KernelMorphism.dualLineKernelMorphismPullback f (Dual.ParameterLineKernel.dualParameterLineKernel D.poincare D.normalizedAtDualZero.some t) *
        DualLine.KernelMorphism.dualLineKernelMorphismPullback g (Dual.ParameterLineKernel.dualParameterLineKernel D.poincare D.normalizedAtDualZero.some t) := by
  apply Subtype.ext
  change HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ (f * g)).left
      (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass D.poincare t.val) =
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass D.poincare t.val) *
      HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ g).left (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass D.poincare t.val)
  rw [poincareParameterPullback_pair A D X (f * g) t.val,
    poincareParameterPullback_pair A D X f t.val, poincareParameterPullback_pair A D X g t.val,
    MonObj.comp_mul, (D.poincarePairClass (LieRanks.dualNumberTest ℂ ⊗ X) _).map_mul]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareParameterPullbackPair
