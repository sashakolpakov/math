import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualTranslation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ThetaConstructionCubicalPolarization
import OAI.RepresentationTheory.Theta.Geometric.QuotientPicardClass

/-! # Integral Dual Cubical -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualCubical.Geometric.AlgebraicPeriodModel

noncomputable section

/-! The same primitive ample ThetaConstruction theta bundle is cubical and invariant
under the actual integral-dual translations. Its native Chern pairing
is the original prescribed integral pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

open OAI.RepresentationTheory.Theta.Geometric.QuotientPicardClass

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} {T : DefinitionsIntegral.MarkedPolarizedTorus g E}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel T) (hE : E.transpose = -E)

local instance : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

theorem _root_.OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.exists_primitive_cubical_integralDual_invariant_theta :
    ∃ (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (T.polarizationFactor hE))
      (jU : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
      (jV : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension)),
      0 < U.degree ∧ V.degree = U.degree + 1 ∧
      IsClosedImmersion jU.left ∧ IsClosedImmersion jV.left ∧
      (∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map jU (M.period t) =
        ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t)) ∧
      (∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map jV (M.period t) =
        ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t)) ∧
      let L := RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left
      L.IsAmple ∧ RepresentationTheory.Theta.Geometric.Intrinsic.CubeClass.nativeCubeDefect M.abelian (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1 ∧
      (∀ l m : T.lattice, AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian L
        (M.nativeIntegralPeriod l) (M.nativeIntegralPeriod m) = (DefinitionsIntegral.Geometric.integralLatticeForm T l m : ℚ)) ∧
      ∀ a : T.integralDualLattice,
        Nonempty ((L.pullback (RepresentationTheory.Theta.Geometric.AlgebraicTranslation.abelianTranslation M.abelian
          (M.period (QuotientAddGroup.mk a.val))).left).sheaf ≅ L.sheaf) := by
  obtain ⟨U, V, jU, jV, hpos, hdeg, hUi, hVi, hUd, hVd, hjU, hjV, heU, heV, _hline, hamp⟩ :=
    M.exists_ample_theta_quotient (hP := hE)
  refine ⟨U, V, jU, jV, hpos, hdeg, hjU, hjV, heU, heV, hamp, ?_, ?_, ?_⟩
  · exact RepresentationTheory.Theta.Geometric.Intrinsic.CubicalClass.native_cubical_theta_quotient_class U V (AbelianModuli.ReferenceFamily.ThetaConstructionCubicalPolarization.e36PolarizationFactor_cubical T hE)
      hUi hVi hUd hVd M.abelian M.period M.period_add jU jV heU heV
  · exact M.nativeThetaChernForm_integral U V jU jV heU heV hdeg
  · intro a
    exact RepresentationTheory.Theta.Geometric.QuotientPicardClass.thetaQuotient_preserved_of_hyperplanes jU.left jV.left _
      (M.integralDual_hyperplane_iso hE U hUi hUd jU heU a)
      (M.integralDual_hyperplane_iso hE V hVi hVd jV heV a)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualCubical.Geometric.AlgebraicPeriodModel
