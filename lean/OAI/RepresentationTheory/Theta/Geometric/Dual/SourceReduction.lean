import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.MapFirstJet
import OAI.RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction

/-! # Source Reduction -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.SourceReduction

noncomputable section

/-! A native infinitesimal period translation reduces to the original
period point on every projective theta chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.Manifold

theorem dualSource_reduction_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (p : V → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z a : V)
    (t : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X ⟶ X)
    (ht : AffineBaseChangeChart.dualConstantPoint X (p z) ≫ t = Intrinsic.MapFirstJet.nativeMapFirstJet X p z a) :
    p z ≫ BaseChangeReduction.dualBaseChangeReduction X ≫ t = p z := by
  calc
    _ = (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ ≫ AffineBaseChangeChart.dualConstantPoint X (p z)) ≫ t := by
      rw [BaseChangeReduction.dualConstantPoint_reduction, Category.assoc]
    _ = AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ ≫ Intrinsic.MapFirstJet.nativeMapFirstJet X p z a := by rw [Category.assoc, ht]
    _ = p z := Intrinsic.MapFirstJet.nativeMapFirstJet_reduction X p z a

theorem dualTarget_reduction_eq (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    p ≫ BaseChangeReduction.dualBaseChangeReduction X ≫ snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X = p := by
  simp [BaseChangeReduction.dualBaseChangeReduction]

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.SourceReduction
