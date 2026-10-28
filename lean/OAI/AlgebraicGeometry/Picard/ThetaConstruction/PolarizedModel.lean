import OAI.AlgebraicGeometry.Picard.ThetaConstruction.PolarizationFactor
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport
import OAI.RepresentationTheory.Theta.Geometric.ConsecutiveEmbeddings
import OAI.RepresentationTheory.Theta.Geometric.PowerAlgebraization
import OAI.RepresentationTheory.Theta.Geometric.CanonicalPowerIso
import OAI.RepresentationTheory.Theta.Geometric.QuotientAmpleness

/-! # Polarized Model -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.PolarizedModel.Geometric

noncomputable section

/-! Algebraic theta model of the original ThetaConstruction polarization factor.
Consecutive powers produce an ample algebraic line bundle with a proved
power isomorphism, together with the actual analytic group comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

local instance polarizedThetaModelIntegral (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left :=
  A.variety.property
local instance polarizedThetaModelSmooth (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom :=
  A.variety.presentation.smooth

open OAI.RepresentationTheory.Theta.Geometric.ConsecutiveEmbeddings.CM.Torus.AutomorphicTheta OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} (T : DefinitionsIntegral.MarkedPolarizedTorus g E)

theorem exists_consecutive_theta_families (hE : E.transpose = -E) :
    ∃ U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (PolarizationFactor.Geometric.polarizationFactor T hE),
      0 < U.degree ∧ V.degree = U.degree + 1 ∧
      Function.Injective U.projectiveMap ∧ Function.Injective V.projectiveMap ∧
      (∀ p v : (ProjectivePeriodData.Geometric.projectivePeriodData T).space, v ≠ 0 → U.Detects p v) ∧
      ∀ p v : (ProjectivePeriodData.Geometric.projectivePeriodData T).space, v ≠ 0 → V.Detects p v := by
  have hint : ∀ u ∈ (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice,
      ∀ v ∈ (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice,
      ∃ m : ℤ, (T.riemannForm u v).im = (m : ℝ) := by
    intro u hu v hv
    exact ⟨DefinitionsIntegral.Geometric.integralLatticeForm T ⟨u, hu⟩ ⟨v, hv⟩,
      DefinitionsIntegral.Geometric.integralLatticeForm_riemann T ⟨u, hu⟩ ⟨v, hv⟩⟩
  exact RepresentationTheory.Theta.Geometric.ConsecutiveEmbeddings.CM.Torus.AutomorphicTheta.exists_consecutive_embeddings (Φ := ProjectivePeriodData.Geometric.projectivePeriodData T)
    T.riemannForm T.hermitian T.positive hint (PolarizationFactor.Geometric.polarizationFactor T hE)
    (PolarizationFactor.Geometric.polarizationFactor_contDiff T hE) (PolarizationFactor.Geometric.polarizationFactor_square T hE)
    (PolarizationFactor.Geometric.polarizationFactor_double_lattice T hE)

/-- An actual algebraic group model, with consecutive theta embeddings
for the specified polarization and an ample quotient of their line bundles. -/
theorem exists_ample_theta_model (hE : E.transpose = -E) :
    ∃ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
      (e : (ProjectivePeriodData.Geometric.projectivePeriodData T).periodTorus ≃ₘ⟮𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData T).space),
        𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)⟯ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
      (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (PolarizationFactor.Geometric.polarizationFactor T hE))
      (jU : A.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
      (jV : A.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension)),
      (∀ u v, e (u + v) = e u * e v) ∧
      0 < U.degree ∧ V.degree = U.degree + 1 ∧
      IsClosedImmersion jU.left ∧ IsClosedImmersion jV.left ∧
      (∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map jU (e t) =
        ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t)) ∧
      (∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map jV (e t) =
        ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t)) ∧
      Nonempty (AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left).sheaf U.degree ≅
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback jU.left (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicTwistBundle U.projectiveDimension 1)).sheaf) ∧
      (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left).IsAmple := by
  obtain ⟨U, V, hpos, hdeg, hUi, hVi, hUd, hVd⟩ := exists_consecutive_theta_families T hE
  obtain ⟨A, e, jU, jV, hjU, hjV, he, heU, heV⟩ :=
    RepresentationTheory.Theta.Geometric.TwoAlgebraizations.CM.Torus.AutomorphicTheta.two_algebraic_embeddings U V hUi hVi hUd hVd
  let : IsIntegral A.toOver.left := A.variety.property
  let : Smooth A.toOver.hom := A.variety.presentation.smooth
  let : IsProper A.toOver.hom := A.variety.presentation.projective.isProper
  obtain ⟨jW, _, heW⟩ := U.commonPower_algebraic_embedding V
    (by omega : 0 < V.degree) hUi hUd A e he
  obtain ⟨a⟩ := RepresentationTheory.Theta.Geometric.CanonicalPowerIso.canonicalThetaQuotientPower_iso U V hpos hdeg jW jU jV
    e e.surjective heW heU heV
  let : IsClosedImmersion jU.left := hjU
  let : CompactSpace A.toOver.left := QuasiCompact.compactSpace_of_compactSpace A.toOver.hom
  exact ⟨A, e, U, V, jU, jV, he, hpos, hdeg, hjU, hjV, heU, heV, ⟨a⟩,
    RepresentationTheory.Theta.Geometric.QuotientAmpleness.thetaQuotient_isAmple_of_power_iso jU.left jV.left U.degree hpos a⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.PolarizedModel.Geometric
