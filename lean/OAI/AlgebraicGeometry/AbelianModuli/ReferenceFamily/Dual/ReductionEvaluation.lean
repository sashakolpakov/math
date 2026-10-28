import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.TopSectionValues
import OAI.RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction
import OAI.RepresentationTheory.Theta.Geometric.Dual.OpenSectionValues

/-! # Reduction Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ReductionEvaluation

noncomputable section

/-! The constant coefficient of an actual dual-number section value
is evaluation on the original reduced fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

theorem dualReduction_sectionValue (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (s : Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, ⊤)) :
    (RepresentationTheory.Theta.Geometric.Dual.SectionEvaluation.dualGlobalSectionValue (RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualConstantPoint X p).left s).fst =
      RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue p.left ⊤ (by trivial) ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left.appTop s) := by
  have hpoint : (LieRanks.dualNumberOrigin ℂ).left ≫ (RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualConstantPoint X p).left =
      p.left ≫ (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left :=
    congrArg (fun q : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ LieRanks.dualNumberTest ℂ ⊗ X => q.left)
      (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualConstantPoint_reduction X p)
  have he := RepresentationTheory.Theta.Geometric.Dual.OpenSectionValues.dualGlobalSectionValue_fst (RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualConstantPoint X p).left s
  have hc := RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue_congr _ _ hpoint ⊤ (by trivial) (by trivial) s
  exact he.trans (hc.trans (Complex.TopSectionValues.complexSectionValue_top_pullback p.left
    (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left s))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ReductionEvaluation
