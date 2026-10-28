import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualIsogenyKernel
import OAI.RepresentationTheory.Theta.Geometric.Dual.LatticeTranslation
import OAI.RepresentationTheory.Theta.Geometric.TranslationAlgebraization

/-! # Integral Dual Translation -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualTranslation.Geometric

noncomputable section

/-! Every actual integral-dual vector preserves the original ThetaConstruction theta
bundle through an explicit holomorphic translation gauge. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} (T : DefinitionsIntegral.MarkedPolarizedTorus g E) (hE : E.transpose = -E)

theorem integralDualTranslation_automorphy (a : T.integralDualLattice)
    (l : (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice) (w : (ProjectivePeriodData.Geometric.projectivePeriodData T).space) :
    RepresentationTheory.Theta.Geometric.Dual.LatticeTranslation.polarizationTranslationGauge T.riemannForm a.val (w + l.val) *
      (PolarizationFactor.Geometric.polarizationFactor T hE).value l (w + (show (ProjectivePeriodData.Geometric.projectivePeriodData T).space from a.val)) =
        (PolarizationFactor.Geometric.polarizationFactor T hE).value l w * RepresentationTheory.Theta.Geometric.Dual.LatticeTranslation.polarizationTranslationGauge T.riemannForm a.val w := by
  have hint : ∃ m : ℤ, (T.riemannForm a.val l.val).im = (m : ℝ) := by
    obtain ⟨m, hm⟩ := Submodule.mem_one.mp (a.property l.val l.property)
    exact ⟨m, hm.symm⟩
  exact RepresentationTheory.Theta.Geometric.Dual.LatticeTranslation.polarizationTranslationGauge_automorphy (DefinitionsIntegral.Geometric.integralLatticeBasis T) (DefinitionsIntegral.Geometric.integralLatticeForm T)
    T.lattice.subtype T.riemannForm T.hermitian a.val l hint w

def integralDualTranslateSection (a : T.integralDualLattice) {n : ℕ}
    (s : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section (PolarizationFactor.Geometric.polarizationFactor T hE) n) : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section (PolarizationFactor.Geometric.polarizationFactor T hE) n :=
  s.translateByGauge a.val (RepresentationTheory.Theta.Geometric.Dual.LatticeTranslation.polarizationTranslationGauge T.riemannForm a.val)
    ((RepresentationTheory.Theta.Geometric.Dual.LatticeTranslation.polarizationTranslationGauge_contDiff T.riemannForm a.val).of_le (by norm_num))
    (integralDualTranslation_automorphy T hE a)

namespace AlgebraicPeriodModel
variable {T} (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

local instance : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

theorem _root_.OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.integralDual_hyperplane_iso (U : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (PolarizationFactor.Geometric.polarizationFactor T hE))
    (hUi : Function.Injective U.projectiveMap)
    (hUd : ∀ p v : (ProjectivePeriodData.Geometric.projectivePeriodData T).space, v ≠ 0 → U.Detects p v)
    (j : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (he : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t)) (a : T.integralDualLattice) :
    Nonempty (((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback j.left (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicTwistBundle U.projectiveDimension 1)).pullback
      (RepresentationTheory.Theta.Geometric.AlgebraicTranslation.abelianTranslation M.abelian (M.period (QuotientAddGroup.mk a.val))).left).sheaf ≅
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback j.left (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicTwistBundle U.projectiveDimension 1)).sheaf) :=
  RepresentationTheory.Theta.Geometric.TranslationAlgebraization.thetaTranslation_algebraic_iso U hUi hUd (integralDualTranslateSection T hE a) a.val
    (RepresentationTheory.Theta.Geometric.Dual.LatticeTranslation.polarizationTranslationGauge T.riemannForm a.val)
    (RepresentationTheory.Theta.Geometric.Dual.LatticeTranslation.polarizationTranslationGauge_ne_zero T.riemannForm a.val)
    (fun _ _ => rfl) M.abelian M.period M.period_add j he

end AlgebraicPeriodModel

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualTranslation.Geometric
