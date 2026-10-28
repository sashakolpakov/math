import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.AnalytificationOpenFrames
import OAI.AlgebraicGeometry.Comparison.Betti.Finite.FreeSheafSections

/-! # Analytified Open Section Bases -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AnalytifiedOpenSectionBases

noncomputable section

/-! The original analytified modules have genuine finite free section bases inside standard smooth algebraic opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom] (U : X.left.Opens)
  [IsAffine (Open.AffineIsoEvaluation.openOver X U).left]
  [Algebra.IsStandardSmooth ℂ (Affine.ExteriorRestrictions.globalCoordinateAlgebra (Open.AffineIsoEvaluation.openOver X U))]

def standardSmoothOpenAnalytifiedSectionBasis (n : ℕ)
    (W : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hW : W ≤ Open.AffineIsoEvaluation.analyticOpen X U) :
    Module.Basis (Betti.Smooth.ExteriorFrames.exteriorFrameIndex (Open.AffineIsoEvaluation.openOver X U) n) ((Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X).obj.obj (op W))
      (((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n)).val.obj (op W)) := by
  let : Module (((Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X).over (Open.AffineIsoEvaluation.analyticOpen X U)).obj.obj
      (op (Over.mk (homOfLE hW))))
      (((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n)).val.obj (op W)) :=
    inferInstanceAs (Module ((Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X).obj.obj (op W))
      (((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n)).val.obj (op W)))
  exact (Finite.FreeSheafSections.RingedModules.finiteFreeSheafSectionBasis
    ((Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)).over (Open.AffineIsoEvaluation.analyticOpen X U))
    ((Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X).over (Open.AffineIsoEvaluation.analyticOpen X U))
    (Betti.Smooth.ExteriorFrames.exteriorFrameIndex (Open.AffineIsoEvaluation.openOver X U) n) (op (Over.mk (homOfLE hW)))).map
      (((SheafOfModules.evaluation ((Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X).over (Open.AffineIsoEvaluation.analyticOpen X U))
        (op (Over.mk (homOfLE hW)))).mapIso (Holomorphic.AnalytificationOpenFrames.analytifiedStandardSmoothOpenFreeIso X U n)).toLinearEquiv)

end

end OAI.AlgebraicGeometry.Comparison.Betti.AnalytifiedOpenSectionBases
