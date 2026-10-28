import OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedInducingFormula
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationFibers

/-! # Framed Subgroup Inducing Product -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedSubgroupInducingProduct

noncomputable section

/-! Construct the subgroup product and translation directly from the symmetric regrouped inducing formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFormulaSymmetry
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation

variable {S : Scheme.{u}} {H A : Over S} [GrpObj A] (i : H ⟶ A)
  (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L : Line.Bundles.LineBundle A.left)
  (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (Line.Fibers.fiber L (fst A A))) (Line.Fibers.fiber L (snd A A)) ≅ Line.Fibers.fiber L μ[A])
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ A).left ≅ (Scheme.Modules.pullback (i ⊗ₘ 𝟙 A).left).obj Q.sheaf)

/-- Identify the external tensor factor with the inducing line at the subgroup element and starting point. -/
def sourceComparison :
    (Scheme.Modules.pullback (i ⊗ₘ 𝟙 A).left).obj (InducingFormulaSymmetry.factorLine A L).sheaf ≅
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (Line.Fibers.fiber L (fst H A ≫ i)) (Line.Fibers.fiber L (snd H A)) :=
  Tensor.LinePullback.pullbackIso (i ⊗ₘ 𝟙 A).left _ _ (Line.Fibers.fiber_isLine L (fst A A)) (Line.Fibers.fiber_isLine L (snd A A)) ≪≫
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr
      (Line.Fibers.fiberPullbackIso L (i ⊗ₘ 𝟙 A) (fst A A) (fst H A ≫ i) (tensorHom_fst i (𝟙 A)))
      (Line.Fibers.fiberPullbackIso L (i ⊗ₘ 𝟙 A) (snd A A) (snd H A)
        ((tensorHom_snd i (𝟙 A)).trans (Category.comp_id _)))

/-- Identify the target with the inducing line at the actual subgroup translation. -/
def targetComparison :
    (Scheme.Modules.pullback (i ⊗ₘ 𝟙 A).left).obj (InducingFormulaSymmetry.targetLine A L).sheaf ≅ Line.Fibers.fiber L (NormalizedKernelTranslation.action i) :=
  Line.Fibers.fiberPullbackIso L (i ⊗ₘ 𝟙 A) μ[A] (NormalizedKernelTranslation.action i) rfl

/-- This product is an actual sheaf isomorphism before any choice of subgroup-line frame. -/
def productIso : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (Line.Fibers.fiber L (fst H A ≫ i)) (Line.Fibers.fiber L (snd H A)) ≅ Line.Fibers.fiber L (NormalizedKernelTranslation.action i) := by
  let z := FramedInducingFormula.product Q L e (i ⊗ₘ 𝟙 A) s
  have hz : IsIso z := FramedInducingFormula.product_isIso Q L e (i ⊗ₘ 𝟙 A) s
  exact (sourceComparison i L).symm ≪≫ @asIso _ _ _ _ z hz ≪≫ targetComparison i L

/-- A frame of the subgroup line turns the actual product into a global translation isomorphism. -/
def translationIso (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule H.left ≅ Line.Fibers.fiber L i) :
    Line.Fibers.fiber L (snd H A) ≅ Line.Fibers.fiber L (NormalizedKernelTranslation.action i) :=
  (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso (Line.Fibers.fiber L (snd H A))).symm ≪≫
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr
      (GlobalPullbackFrame.atPoint i L t (fst H A) (fst H A ≫ i) rfl)
      (Iso.refl (Line.Fibers.fiber L (snd H A))) ≪≫ productIso i Q L e s

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedSubgroupInducingProduct
