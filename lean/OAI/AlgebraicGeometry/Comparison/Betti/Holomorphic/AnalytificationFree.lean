import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.AnalytificationUnit
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.ExteriorFrames

/-! # Analytification Free -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.AnalytificationFree

noncomputable section

/-! Actual analytification carries free differential-module presentations to free analytic presentations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def holomorphicAnalytificationFreeIso (I : Type) :
    (StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj
        (SheafOfModules.free (R := X.left.ringCatSheaf) I) ≅
      SheafOfModules.free (R := StructureMorphism.analyticHolomorphicStructureSheaf X) I :=
  @SheafOfModules.pullbackObjFreeIso
    (Opens X.left) inferInstance (Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) inferInstance
    (Opens.grothendieckTopology X.left) (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (Opens.map (Analytification.Base.analytificationMap X)) X.left.ringCatSheaf (StructureMorphism.analyticHolomorphicStructureSheaf X)
    (StructureMorphism.holomorphicAnalytificationSite_continuous X) (StructureMorphism.algebraicToHolomorphicStructureSheaf X)
    (StructureMorphism.holomorphicModuleDirectImage_isRightAdjoint X) inferInstance inferInstance
    inferInstance inferInstance (AnalytificationUnit.holomorphicAnalytificationSite_final X) I

def standardSmoothAnalytifiedExteriorFreeIso [IsAffine X.left]
    [Algebra.IsStandardSmooth ℂ (Affine.ExteriorRestrictions.globalCoordinateAlgebra X)] (n : ℕ) :
    SheafOfModules.free (R := StructureMorphism.analyticHolomorphicStructureSheaf X) (Betti.Smooth.ExteriorFrames.exteriorFrameIndex X n) ≅
      (StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n) :=
  (holomorphicAnalytificationFreeIso X (Betti.Smooth.ExteriorFrames.exteriorFrameIndex X n)).symm ≪≫
    (StructureMorphism.algebraicModuleHolomorphicAnalytification X).mapIso (Betti.Smooth.ExteriorFrames.standardSmoothExteriorFreeIso X n)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.AnalytificationFree
