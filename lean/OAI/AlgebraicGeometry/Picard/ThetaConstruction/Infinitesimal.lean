import OAI.AlgebraicGeometry.Picard.ThetaConstruction.InfinitesimalPeriod
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.FirstJetGauge
import OAI.RepresentationTheory.Theta.Geometric.GlobalDualGauge
import OAI.RepresentationTheory.Theta.Geometric.IteratedQuotientIso
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.DualZero

/-! # Infinitesimal -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! An actual infinitesimal translation preserving the original ample
theta quotient has zero native parameter. The comparison gauge is
constructed from the given sheaf isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim}
    {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix} {hP : matrix.transpose = -matrix}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel F)

local instance PeriodModel.Geometric.AlgebraicPeriodModel.infinitesimalTheta_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.infinitesimalTheta_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

theorem PeriodModel.Geometric.AlgebraicPeriodModel.nativeInfinitesimalTheta_eq_one (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (PolarizationFactor.Geometric.polarizationFactor F hP))
    (hdeg : V.degree = U.degree + 1)
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) = ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension
      (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) = ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension
      (V.projectiveMap t))
    (r : AbelianModuli.ReferenceFamily.DualOpen.Lifts.DualSchemePoints M.abelian.toOver 1)
    (u : (((RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left).pullback
      (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) M.abelianScheme.scheme).left).pullback
        (M.abelianScheme.translation r.val).left).sheaf ≅
      ((RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left).pullback
        (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) M.abelianScheme.scheme).left).sheaf) : r.val = 1 := by
  obtain ⟨a, ha, htranslate⟩ := M.exists_infinitesimal_period_direction r
  let τ : AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ M.abelian.toOver ⟶ AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ M.abelian.toOver :=
    M.abelianScheme.translation r.val
  let t : AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ M.abelian.toOver ⟶ M.abelian.toOver :=
    τ ≫ snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) M.abelian.toOver
  have e : (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient (t ≫ f).left (t ≫ g).left).sheaf ≅
      (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) M.abelian.toOver ≫ f).left
        (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) M.abelian.toOver ≫ g).left).sheaf := by
    simpa only [t, Over.comp_left, Category.assoc] using
      RepresentationTheory.Theta.Geometric.IteratedQuotientIso.iteratedThetaQuotientIso f.left g.left
        (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) M.abelian.toOver).left
        τ.left u
  have ht : ∀ w, RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualConstantPoint M.abelian.toOver (M.vectorPeriod w) ≫ t =
      RepresentationTheory.Theta.Geometric.Intrinsic.MapFirstJet.nativeMapFirstJet M.abelian.toOver M.vectorPeriod w a := fun w => htranslate w
  have hp := M.vectorPeriod_contMDiff.mdifferentiable (by simp)
  have hperiod : ∀ (l : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodIntegerLattice) w,
      M.vectorPeriod (w + l.val) = M.vectorPeriod w := by
    intro l w
    apply congrArg M.period
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    have hw : w + l.val - w = l.val := by abel
    rw [hw]
    exact l.property
  have hJ : ∀ l : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodIntegerLattice,
      Differentiable ℂ ((PolarizationFactor.Geometric.polarizationFactor F hP).value l) := fun l =>
    (PolarizationFactor.Geometric.polarizationFactor_contDiff F hP l).differentiable (by simp)
  obtain ⟨c, hc, hunit, hcocycle⟩ := RepresentationTheory.Theta.Geometric.GlobalDualGauge.exists_globalDualThetaGauge U V hdeg f g t e M.vectorPeriod a ht
    (fun w => hf (QuotientAddGroup.mk w)) (fun w => hg (QuotientAddGroup.mk w)) hp hperiod hJ
  have ha0 : a = 0 := F.firstJetGauge_eq_zero hP a c hc (hunit 0) hcocycle
  have hr : r.val = RepresentationTheory.Theta.Geometric.Intrinsic.MapFirstJet.nativeMapFirstJet M.abelian.toOver M.vectorPeriod 0 0 := by
    rw [ha0] at ha
    exact ha.symm
  rw [hr, RepresentationTheory.Theta.Geometric.Intrinsic.DualZero.nativeMapFirstJet_zero, M.vectorPeriod_zero, MonObj.comp_one]

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
