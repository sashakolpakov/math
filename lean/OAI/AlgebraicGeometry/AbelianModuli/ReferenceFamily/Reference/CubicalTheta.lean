import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.Embedding
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.Translation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.CubicalFactor
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CubicalClass
import OAI.RepresentationTheory.Theta.Geometric.QuotientPicardClass

/-! # Cubical Theta -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! The chosen reference abelian model carries a constructed ample
cubical line bundle preserved by the actual lattice-isogeny kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance AlgebraicModel.ReferenceAlgebraicModel.cubicalTheta_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance AlgebraicModel.ReferenceAlgebraicModel.cubicalTheta_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

theorem AlgebraicModel.ReferenceAlgebraicModel.exists_cubical_kernel_invariant_theta :
    ∃ (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))
      (jU : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
      (jV : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension)),
      0 < U.degree ∧ V.degree = U.degree + 1 ∧
      IsClosedImmersion jU.left ∧ IsClosedImmersion jV.left ∧
      (∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map jU (M.period t) =
        ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t)) ∧
      (∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map jV (M.period t) =
        ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t)) ∧
      (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left).IsAmple ∧
      RepresentationTheory.Theta.Geometric.Intrinsic.CubeClass.nativeCubeDefect M.abelian (HilbertConstruction.Line.Bundles.LineBundle.classOf (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left)) = 1 ∧
      ∀ a : F.dualLattice,
        Nonempty (((RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left).pullback
          (RepresentationTheory.Theta.Geometric.AlgebraicTranslation.abelianTranslation M.abelian (M.period (QuotientAddGroup.mk a.val))).left).sheaf ≅
          (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left).sheaf) := by
  obtain ⟨U, V, jU, jV, hpos, hdeg, hUi, hVi, hUd, hVd, hjU, hjV, heU, heV, _, hamp⟩ :=
    M.exists_ample_theta_quotient
  refine ⟨U, V, jU, jV, hpos, hdeg, hjU, hjV, heU, heV, hamp, ?_, fun a => ?_⟩
  · exact RepresentationTheory.Theta.Geometric.Intrinsic.CubicalClass.native_cubical_theta_quotient_class U V (F.polarizationFactor_isCubical hP)
      hUi hVi hUd hVd M.abelian M.period M.period_add jU jV heU heV
  · exact RepresentationTheory.Theta.Geometric.QuotientPicardClass.thetaQuotient_preserved_of_hyperplanes jU.left jV.left _
      (M.kernel_hyperplane_iso U hUi hUd jU heU a) (M.kernel_hyperplane_iso V hVi hVd jV heV a)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
