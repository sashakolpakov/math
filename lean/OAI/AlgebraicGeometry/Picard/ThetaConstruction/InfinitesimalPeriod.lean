import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualModel
import OAI.RepresentationTheory.Theta.Geometric.VectorPeriodDualPoints
import OAI.RepresentationTheory.Theta.Geometric.Dual.FamilyTranslationPoints

/-! # Infinitesimal Period -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! Actual dual-number points of the ThetaConstruction algebraic model are period jets;
relative translation transports each jet to every period point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim}
    {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel F)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.exists_infinitesimal_period_direction (r : AbelianModuli.ReferenceFamily.DualOpen.Lifts.DualSchemePoints M.abelian.toOver 1) :
    ∃ a : (ProjectivePeriodData.Geometric.projectivePeriodData F).space,
      RepresentationTheory.Theta.Geometric.VectorPeriodDualPoints.vectorPeriodDualPoint M.abelian M.period 0 a = r.val ∧
      ∀ w : (ProjectivePeriodData.Geometric.projectivePeriodData F).space,
        RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualConstantPoint M.abelianScheme.scheme (M.vectorPeriod w) ≫
          M.abelianScheme.translation r.val ≫ snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) M.abelianScheme.scheme =
            RepresentationTheory.Theta.Geometric.VectorPeriodDualPoints.vectorPeriodDualPoint M.abelian M.period w a := by
  let r' : AbelianModuli.ReferenceFamily.DualOpen.Lifts.DualSchemePoints M.abelian.toOver (M.period (QuotientAddGroup.mk 0)) :=
    ⟨r.val, r.property.trans M.vectorPeriod_zero.symm⟩
  obtain ⟨a, ha⟩ := RepresentationTheory.Theta.Geometric.VectorPeriodDualPoints.exists_vectorPeriodDualPoint M.abelian M.period 0 r'
  refine ⟨a, ha, ?_⟩
  intro w
  have ht := RepresentationTheory.Theta.Geometric.VectorPeriodDualPoints.vectorPeriodDualPoint_translates M.abelian M.period M.period_add 0 w a
  have ht' : RepresentationTheory.Theta.Geometric.VectorPeriodDualPoints.vectorPeriodDualPoint M.abelian M.period w a =
      r.val ≫ RepresentationTheory.Theta.Geometric.AlgebraicTranslation.abelianTranslation M.abelian (M.vectorPeriod w) := by
    simpa only [zero_add, ha, r', PeriodModel.Geometric.AlgebraicPeriodModel.vectorPeriod] using ht
  exact (RepresentationTheory.Theta.Geometric.Dual.FamilyTranslationPoints.dualConstantPoint_translation_snd M.abelianScheme r.val (M.vectorPeriod w)).trans
    ((RepresentationTheory.Theta.Geometric.VectorPeriodDualPoints.abelianTranslation_dualPoint M.abelian (M.vectorPeriod w) r.val).symm.trans ht'.symm)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
