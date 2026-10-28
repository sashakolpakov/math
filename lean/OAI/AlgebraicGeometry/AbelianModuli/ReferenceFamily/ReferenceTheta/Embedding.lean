import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PolarizationFactor
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.Families
import OAI.RepresentationTheory.Theta.Geometric.PowerAlgebraization
import OAI.RepresentationTheory.Theta.Geometric.CanonicalPowerIso
import OAI.RepresentationTheory.Theta.Geometric.QuotientAmpleness

/-! # Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Consecutive powers of the original reference polarization factor
give actual projective embeddings on the already constructed abelian
model. Their algebraic quotient is ample, and a positive power is
identified with the first hyperplane bundle by an actual sheaf isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaEmbedding_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaEmbedding_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaEmbedding_proper : IsProper M.abelian.toOver.hom := M.abelian.variety.presentation.projective.isProper

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.exists_ample_theta_quotient :
    ∃ (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))
      (jU : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
      (jV : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension)),
      0 < U.degree ∧ V.degree = U.degree + 1 ∧
      Function.Injective U.projectiveMap ∧ Function.Injective V.projectiveMap ∧
      (∀ p v : F.periodData.space, v ≠ 0 → U.Detects p v) ∧
      (∀ p v : F.periodData.space, v ≠ 0 → V.Detects p v) ∧
      IsClosedImmersion jU.left ∧ IsClosedImmersion jV.left ∧
      (∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map jU (M.period t) =
        ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t)) ∧
      (∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map jV (M.period t) =
        ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t)) ∧
      Nonempty (HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left).sheaf U.degree ≅
        (HilbertConstruction.Line.Bundles.LineBundle.pullback jU.left (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicTwistBundle U.projectiveDimension 1)).sheaf) ∧
      (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left).IsAmple := by
  obtain ⟨U, V, hpos, hdeg, hUi, hVi, hUd, hVd⟩ := F.exists_consecutive_theta_families hP
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

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
