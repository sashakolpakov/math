import OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.PolarizedModel

/-! # Embedding On Model -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! Consecutive original theta powers on the constructed ThetaConstruction algebraic model.
This source is pending Lean validation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim}
    {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix} {hP : matrix.transpose = -matrix}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel F)

local instance PeriodModel.Geometric.AlgebraicPeriodModel.thetaEmbedding_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.thetaEmbedding_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance PeriodModel.Geometric.AlgebraicPeriodModel.thetaEmbedding_proper : IsProper M.abelian.toOver.hom := M.abelian.variety.presentation.projective.isProper

theorem PeriodModel.Geometric.AlgebraicPeriodModel.exists_ample_theta_quotient :
    ∃ (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family ((PolarizationFactor.Geometric.polarizationFactor F) hP))
      (jU : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
      (jV : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension)),
      0 < U.degree ∧ V.degree = U.degree + 1 ∧
      Function.Injective U.projectiveMap ∧ Function.Injective V.projectiveMap ∧
      (∀ p v : (ProjectivePeriodData.Geometric.projectivePeriodData F).space, v ≠ 0 → U.Detects p v) ∧
      (∀ p v : (ProjectivePeriodData.Geometric.projectivePeriodData F).space, v ≠ 0 → V.Detects p v) ∧
      IsClosedImmersion jU.left ∧ IsClosedImmersion jV.left ∧
      (∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map jU (M.period t) =
        ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t)) ∧
      (∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map jV (M.period t) =
        ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t)) ∧
      Nonempty (AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left).sheaf U.degree ≅
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback jU.left (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicTwistBundle U.projectiveDimension 1)).sheaf) ∧
      (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left).IsAmple := by
  obtain ⟨U, V, hpos, hdeg, hUi, hVi, hUd, hVd⟩ := PolarizedModel.Geometric.exists_consecutive_theta_families F hP
  obtain ⟨jU, hjU, heU⟩ := U.algebraic_embedding_on_model hUi hUd M.abelian M.period M.period_add
  obtain ⟨jV, hjV, heV⟩ := V.algebraic_embedding_on_model hVi hVd M.abelian M.period M.period_add
  have hVpos : 0 < V.degree := by omega
  obtain ⟨jW, _, heW⟩ := U.commonPower_algebraic_embedding V hVpos hUi hUd
    M.abelian M.period M.period_add
  obtain ⟨a⟩ := RepresentationTheory.Theta.Geometric.CanonicalPowerIso.canonicalThetaQuotientPower_iso U V hpos hdeg jW jU jV
    M.period M.period.surjective heW heU heV
  let : IsClosedImmersion jU.left := hjU
  let : CompactSpace M.abelian.toOver.left := QuasiCompact.compactSpace_of_compactSpace M.abelian.toOver.hom
  exact ⟨U, V, jU, jV, hpos, hdeg, hUi, hVi, hUd, hVd, hjU, hjV, heU, heV, ⟨a⟩,
    RepresentationTheory.Theta.Geometric.QuotientAmpleness.thetaQuotient_isAmple_of_power_iso jU.left jV.left U.degree hpos a⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
