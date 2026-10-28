import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.ComplexConstants
import OAI.AlgebraicGeometry.SheafCohomology.Scalars

/-! # Structure Complex Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructureComplexScalars

noncomputable section

/-! Complex scalars on original algebraic H1 come from its actual
global-functions action and the specified complex structure morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

@[instance_reducible]
def structureH1ComplexModule (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) : Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule X.left) 1) := by
  letI := SheafCohomology.AffineH.Projective.globalSectionsCohomologyModule (HilbertConstruction.Line.Bundles.structureModule X.left) 1
  exact Module.compHom (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule X.left) 1) (Open.ComplexConstants.complexGlobalSectionMap X)

theorem structureH1ComplexModule_native (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    structureH1ComplexModule A.toOver = SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule A (HilbertConstruction.Line.Bundles.structureModule A.carrier) 1 := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructureComplexScalars
