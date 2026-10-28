import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ClassKernel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Lifts
import OAI.RepresentationTheory.Theta.Geometric.ParameterizedPicardClass

/-! # Parameter Line Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ParameterLineKernel

noncomputable section

/-! The actual family at a dual-number parameter based at the
identity defines an element of the original line-class reduction kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {A P : Over Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj P]
    (Q : HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A).left)
    (e : (Q.pullback (lift (1 : A ⟶ P) (𝟙 A)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule A.left)

theorem dualParameter_reduction (t : DualOpen.Lifts.DualSchemePoints P 1) :
    RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction A ≫ (t.val ⊗ₘ 𝟙 A) = lift (1 : A ⟶ P) (𝟙 A) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, tensorHom_fst, lift_fst, RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction,
      lift_fst_assoc, Category.assoc, t.property, MonObj.comp_one]
  · simp [RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction]

include e in
theorem dualParameterLineClass_reduces (t : DualOpen.Lifts.DualSchemePoints P 1) :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction A).left (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass Q t.val) = 1 := by
  have h₁ := HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction A).left
    (t.val ⊗ₘ 𝟙 A).left (HilbertConstruction.Line.Bundles.LineBundle.classOf Q)
  have h₂ := congrArg (fun f : A ⟶ P ⊗ A => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left (HilbertConstruction.Line.Bundles.LineBundle.classOf Q))
    (dualParameter_reduction t)
  exact h₁.symm.trans (h₂.trans (Quotient.sound ⟨e⟩))

def dualParameterLineKernel (t : DualOpen.Lifts.DualSchemePoints P 1) : DualLine.ClassKernel.dualLineClassKernel A :=
  ⟨RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass Q t.val, dualParameterLineClass_reduces Q e t⟩

theorem dualParameterLineKernel_injective
    (hinj : Function.Injective (fun t : LieRanks.dualNumberTest ℂ ⟶ P => RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q t)) :
    Function.Injective (dualParameterLineKernel Q e) := by
  intro a b h
  apply Subtype.ext
  apply hinj
  exact congrArg ((HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op (LieRanks.dualNumberTest ℂ))) (congrArg Subtype.val h)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ParameterLineKernel
