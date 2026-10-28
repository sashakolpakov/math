import OAI.RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranslationBaseChange

/-! # Family Translation Points -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.FamilyTranslationPoints

noncomputable section

/-! Evaluation of the actual relative translation at a constant
dual-number point gives the product of the parameter and that point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem dualConstantPoint_translation_snd {d : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (r : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ A.scheme) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) :
    AffineBaseChangeChart.dualConstantPoint A.scheme p ≫ A.translation r ≫ snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) A.scheme =
      r * (toUnit (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ≫ p) := by
  simp only [A.translation_snd, MonObj.comp_mul, ← Category.assoc]
  simp only [AffineBaseChangeChart.dualConstantPoint, lift_fst, Category.id_comp, lift_snd]

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.FamilyTranslationPoints
