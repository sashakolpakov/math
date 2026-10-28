import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.KernelMorphism
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ParameterLineKernel

/-! # Parameter Poincare Square -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ParameterPoincareSquare

noncomputable section

/-! Equality of the original Poincare bundle pullbacks transports
actual infinitesimal parameter line classes through the original
scheme morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {X Y P Q : Over Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj P] [GrpObj Q]
    (f : X ⟶ Y) (d : Q ⟶ P) [IsMonHom d]
    (L : HilbertConstruction.Line.Bundles.LineBundle (P ⊗ X).left) (K : HilbertConstruction.Line.Bundles.LineBundle (Q ⊗ Y).left)
    (eL : (L.pullback (lift (1 : X ⟶ P) (𝟙 X)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule X.left)
    (eK : (K.pullback (lift (1 : Y ⟶ Q) (𝟙 Y)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule Y.left)

def dualPointPostcompose (t : DualOpen.Lifts.DualSchemePoints Q 1) : DualOpen.Lifts.DualSchemePoints P 1 :=
  ⟨t.val ≫ d, by rw [← Category.assoc, t.property, MonObj.one_comp]⟩

theorem dualParameterLineKernel_poincareSquare
    (h : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d ⊗ₘ 𝟙 X).left (HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 Q ⊗ₘ f).left (HilbertConstruction.Line.Bundles.LineBundle.classOf K))
    (t : DualOpen.Lifts.DualSchemePoints Q 1) :
    ParameterLineKernel.dualParameterLineKernel L eL (dualPointPostcompose d t) =
      DualLine.KernelMorphism.dualLineKernelMorphismPullback f (ParameterLineKernel.dualParameterLineKernel K eK t) := by
  apply Subtype.ext
  have H := congrArg (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (t.val ⊗ₘ 𝟙 X).left) h
  rw [← HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp,
    ← Over.comp_left, ← Over.comp_left] at H
  simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id] at H
  have hr := HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left
    (t.val ⊗ₘ 𝟙 Y).left (HilbertConstruction.Line.Bundles.LineBundle.classOf K)
  rw [← Over.comp_left, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id] at hr
  exact H.trans hr

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ParameterPoincareSquare
