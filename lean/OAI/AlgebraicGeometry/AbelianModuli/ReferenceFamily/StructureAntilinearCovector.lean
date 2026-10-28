import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CechAnalytificationLinear
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DolbeaultClassScalars
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomogeneousCovector
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AntilinearDualCoordinates

/-! # Structure Antilinear Covector -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructureAntilinearCovector

noncomputable section

/-! At every abelian variety the original algebraic structure-sheaf
H1 injects into the antiholomorphic dual of its native tangent model. -/

open _root_.CategoryTheory

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)

local instance structureCovectorNativeH1Group :
    AddCommGroup (Sheaf.H (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf A.variety.analyticModel A.variety.analyticSpace) 1) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of A.variety.analyticSpace)
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf A.variety.analyticModel A.variety.analyticSpace) 1

def structureH1AntilinearCovector :
    letI := SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule A (HilbertConstruction.Line.Bundles.structureModule A.carrier) 1
    SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.carrier) 1 →ₗ[ℂ]
      (A.variety.analyticModel →ₗ⋆[ℂ] ℂ) := by
  letI := SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule A (HilbertConstruction.Line.Bundles.structureModule A.carrier) 1
  letI := Holomorphic.Scalars.nativeHolomorphicH1Module A.variety.analyticModel A.variety.analyticSpace
  exact (Intrinsic.HomogeneousCovector.nativeType01AntilinearCovector A).comp
    ((RepresentationTheory.Theta.Geometric.Projective.DolbeaultEquiv.projectiveDolbeaultEquiv A.variety).symm.toLinearMap.comp
      ((DolbeaultClassScalars.nativeDolbeaultClassLinearEquiv A.variety.analyticModel A.variety.analyticSpace).symm.toLinearMap.comp
        (CechAnalytificationLinear.structureH1Analytification A)))

theorem structureH1AntilinearCovector_injective :
    Function.Injective (structureH1AntilinearCovector A) :=
  (Intrinsic.HomogeneousCovector.nativeType01AntilinearCovector_injective A).comp
    ((RepresentationTheory.Theta.Geometric.Projective.DolbeaultEquiv.projectiveDolbeaultEquiv A.variety).symm.injective.comp
      ((DolbeaultClassScalars.nativeDolbeaultClassLinearEquiv A.variety.analyticModel A.variety.analyticSpace).symm.injective.comp
        (CechAnalytificationLinear.structureH1Analytification_injective A)))

theorem abelianStructureH1_finiteDimensional :
    letI := SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule A (HilbertConstruction.Line.Bundles.structureModule A.carrier) 1
    FiniteDimensional ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.carrier) 1) := by
  let := SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule A (HilbertConstruction.Line.Bundles.structureModule A.carrier) 1
  let := AntilinearDualCoordinates.antilinearDual_finiteDimensional (Pi.basisFun ℂ (Fin A.variety.complexDimension))
  exact FiniteDimensional.of_injective (structureH1AntilinearCovector A)
    (structureH1AntilinearCovector_injective A)

theorem abelianStructureH1_finrank_le :
    letI := SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule A (HilbertConstruction.Line.Bundles.structureModule A.carrier) 1
    Module.finrank ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.carrier) 1) ≤ A.variety.complexDimension := by
  let := SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule A (HilbertConstruction.Line.Bundles.structureModule A.carrier) 1
  let := AntilinearDualCoordinates.antilinearDual_finiteDimensional (Pi.basisFun ℂ (Fin A.variety.complexDimension))
  exact (LinearMap.finrank_le_finrank_of_injective (structureH1AntilinearCovector_injective A)).trans
    (by simpa only [Fintype.card_fin] using
      AntilinearDualCoordinates.antilinearDual_finrank_le (Pi.basisFun ℂ (Fin A.variety.complexDimension)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructureAntilinearCovector
