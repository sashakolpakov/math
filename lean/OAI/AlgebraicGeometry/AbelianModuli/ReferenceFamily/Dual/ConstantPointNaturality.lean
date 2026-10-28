import OAI.RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.SectionValueTransport

/-! # Constant Point Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ConstantPointNaturality

noncomputable section

/-! Evaluation on constant dual-number points commutes with actual
pullback of regular functions between product schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

theorem dualConstantPoint_sectionValue_natural {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : X ⟶ Y) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (s : Γ((LieRanks.dualNumberTest ℂ ⊗ Y).left, ⊤)) :
    RepresentationTheory.Theta.Geometric.Dual.SectionEvaluation.dualGlobalSectionValue (RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualConstantPoint X p).left
      ((𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left.appTop s) =
        RepresentationTheory.Theta.Geometric.Dual.SectionEvaluation.dualGlobalSectionValue (RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualConstantPoint Y (p ≫ f)).left s := by
  have h : (RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualConstantPoint X p).left ≫ (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left =
      (RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualConstantPoint Y (p ≫ f)).left :=
    congrArg (fun q : LieRanks.dualNumberTest ℂ ⟶ LieRanks.dualNumberTest ℂ ⊗ Y => q.left)
      (RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualConstantPoint_natural f p)
  exact SectionValueTransport.dualSectionValue_transport (RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualConstantPoint X p).left
    (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left (RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualConstantPoint Y (p ≫ f)).left h s

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ConstantPointNaturality
