import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CechAnalytificationLinear
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DolbeaultClassScalars
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DolbeaultSurjection

/-! # Structure Bound -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! The actual algebraic structure-sheaf H1 of the ThetaConstruction algebraic abelian
variety injects complex linearly into its original period tangent space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim}
    {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix} (M : PeriodModel.Geometric.AlgebraicPeriodModel F)

local instance PeriodModel.Geometric.AlgebraicPeriodModel.structureH1Bound_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.structureH1Bound_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

local instance PeriodModel.Geometric.AlgebraicPeriodModel.structureH1Bound_nativeGroup :
    AddCommGroup (Sheaf.H (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1) :=
  AbelianModuli.ReferenceFamily.Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1

def PeriodModel.Geometric.AlgebraicPeriodModel.periodStructureH1Linear :
    letI := SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule M.abelian (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1
    SheafCohomology.AffineH.Projective.H (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1 →ₗ[ℂ] DefinitionsIntegral.Tangent dim := by
  letI := SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule M.abelian (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1
  letI := AbelianModuli.ReferenceFamily.Holomorphic.Scalars.nativeHolomorphicH1Module (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
  exact M.periodDolbeaultCoordinate.comp
    ((AbelianModuli.ReferenceFamily.DolbeaultClassScalars.nativeDolbeaultClassLinearEquiv (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)).symm.toLinearMap.comp (AbelianModuli.ReferenceFamily.CechAnalytificationLinear.structureH1Analytification M.abelian))

theorem PeriodModel.Geometric.AlgebraicPeriodModel.periodStructureH1Linear_injective : Function.Injective M.periodStructureH1Linear :=
  M.periodDolbeaultCoordinate_injective.comp
    ((AbelianModuli.ReferenceFamily.DolbeaultClassScalars.nativeDolbeaultClassLinearEquiv (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)).symm.injective.comp (AbelianModuli.ReferenceFamily.CechAnalytificationLinear.structureH1Analytification_injective M.abelian))

theorem PeriodModel.Geometric.AlgebraicPeriodModel.periodStructureH1_finiteDimensional :
    let := SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule M.abelian (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1
    FiniteDimensional ℂ (SheafCohomology.AffineH.Projective.H (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1) := by
  let := SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule M.abelian (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1
  exact FiniteDimensional.of_injective M.periodStructureH1Linear M.periodStructureH1Linear_injective

theorem PeriodModel.Geometric.AlgebraicPeriodModel.periodStructureH1_finrank_le :
    let := SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule M.abelian (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1
    Module.finrank ℂ (SheafCohomology.AffineH.Projective.H (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1) ≤
      Module.finrank ℂ (DefinitionsIntegral.Tangent dim) := by
  let := SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule M.abelian (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1
  exact LinearMap.finrank_le_finrank_of_injective M.periodStructureH1Linear_injective

theorem PeriodModel.Geometric.AlgebraicPeriodModel.periodStructureH1_finrank_le_dimension :
    let := SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule M.abelian (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1
    Module.finrank ℂ (SheafCohomology.AffineH.Projective.H (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1) ≤ dim := by
  let := SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule M.abelian (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1
  have h := M.periodStructureH1_finrank_le
  change Module.finrank ℂ (SheafCohomology.AffineH.Projective.H (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule M.abelian.carrier) 1) ≤
    Module.finrank ℂ (Fin dim → ℂ) at h
  simpa only [Module.finrank_fin_fun, Fintype.card_fin] using h

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
