import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CechAnalytificationLinear
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DolbeaultClassScalars
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DolbeaultSurjection

/-! # Structure Bound -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! The actual algebraic structure-sheaf H1 of the reference abelian
variety injects complex linearly into its original period tangent space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance AlgebraicModel.ReferenceAlgebraicModel.structureH1Bound_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance AlgebraicModel.ReferenceAlgebraicModel.structureH1Bound_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

local instance AlgebraicModel.ReferenceAlgebraicModel.structureH1Bound_nativeGroup :
    AddCommGroup (Sheaf.H (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1

def AlgebraicModel.ReferenceAlgebraicModel.referenceStructureH1Linear :
    letI := SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule M.abelian (HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1
    SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1 →ₗ[ℂ] F.periodData.space := by
  letI := SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule M.abelian (HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1
  letI := Holomorphic.Scalars.nativeHolomorphicH1Module (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
  exact M.translationDolbeaultEquiv.symm.toLinearMap.comp
    ((DolbeaultClassScalars.nativeDolbeaultClassLinearEquiv (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)).symm.toLinearMap.comp (CechAnalytificationLinear.structureH1Analytification M.abelian))

theorem AlgebraicModel.ReferenceAlgebraicModel.referenceStructureH1Linear_injective : Function.Injective M.referenceStructureH1Linear :=
  M.translationDolbeaultEquiv.symm.injective.comp
    ((DolbeaultClassScalars.nativeDolbeaultClassLinearEquiv (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)).symm.injective.comp (CechAnalytificationLinear.structureH1Analytification_injective M.abelian))

theorem AlgebraicModel.ReferenceAlgebraicModel.referenceStructureH1_finiteDimensional :
    let := SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule M.abelian (HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1
    FiniteDimensional ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1) := by
  let := SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule M.abelian (HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1
  exact FiniteDimensional.of_injective M.referenceStructureH1Linear M.referenceStructureH1Linear_injective

theorem AlgebraicModel.ReferenceAlgebraicModel.referenceStructureH1_finrank_le :
    let := SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule M.abelian (HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1
    Module.finrank ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1) ≤
      Module.finrank ℂ F.periodData.space := by
  let := SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule M.abelian (HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1
  exact LinearMap.finrank_le_finrank_of_injective M.referenceStructureH1Linear_injective

theorem AlgebraicModel.ReferenceAlgebraicModel.referenceStructureH1_finrank_le_dimension :
    let := SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule M.abelian (HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1
    Module.finrank ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1) ≤ 3 * s := by
  let := SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule M.abelian (HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1
  have h := M.referenceStructureH1_finrank_le
  change Module.finrank ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1) ≤
    Module.finrank ℂ (Fin (3 * Fintype.card (Fin s)) → ℂ) at h
  simpa only [Module.finrank_fin_fun, Fintype.card_fin] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
