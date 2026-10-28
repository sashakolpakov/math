import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ModelDerivative
import OAI.RepresentationTheory.Theta.Geometric.VectorPeriodDualPoints
import OAI.RepresentationTheory.Theta.Geometric.Dual.FamilyTranslationPoints

/-! # Infinitesimal Period -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! Actual dual-number points of the reference model are period jets;
relative translation transports each jet to every period point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicModel.ReferenceAlgebraicModel F hP)

theorem AlgebraicModel.ReferenceAlgebraicModel.exists_infinitesimal_period_direction (r : DualOpen.Lifts.DualSchemePoints M.abelian.toOver 1) :
    ∃ a : F.periodData.space,
      RepresentationTheory.Theta.Geometric.VectorPeriodDualPoints.vectorPeriodDualPoint M.abelian M.period 0 a = r.val ∧
      ∀ w : F.periodData.space,
        RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualConstantPoint M.abelianScheme.scheme (M.vectorPeriod w) ≫
          M.abelianScheme.translation r.val ≫ snd (LieRanks.dualNumberTest ℂ) M.abelianScheme.scheme =
            RepresentationTheory.Theta.Geometric.VectorPeriodDualPoints.vectorPeriodDualPoint M.abelian M.period w a := by
  let r' : DualOpen.Lifts.DualSchemePoints M.abelian.toOver (M.period (QuotientAddGroup.mk 0)) :=
    ⟨r.val, r.property.trans M.vectorPeriod_zero.symm⟩
  obtain ⟨a, ha⟩ := RepresentationTheory.Theta.Geometric.VectorPeriodDualPoints.exists_vectorPeriodDualPoint M.abelian M.period 0 r'
  refine ⟨a, ha, ?_⟩
  intro w
  have ht := RepresentationTheory.Theta.Geometric.VectorPeriodDualPoints.vectorPeriodDualPoint_translates M.abelian M.period M.period_add 0 w a
  have ht' : RepresentationTheory.Theta.Geometric.VectorPeriodDualPoints.vectorPeriodDualPoint M.abelian M.period w a =
      r.val ≫ RepresentationTheory.Theta.Geometric.AlgebraicTranslation.abelianTranslation M.abelian (M.vectorPeriod w) := by
    simpa only [zero_add, ha, r', AlgebraicModel.ReferenceAlgebraicModel.vectorPeriod] using ht
  exact (RepresentationTheory.Theta.Geometric.Dual.FamilyTranslationPoints.dualConstantPoint_translation_snd M.abelianScheme r.val (M.vectorPeriod w)).trans
    ((RepresentationTheory.Theta.Geometric.VectorPeriodDualPoints.abelianTranslation_dualPoint M.abelian (M.vectorPeriod w) r.val).symm.trans ht'.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
