import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StructureMorphism
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.ExteriorFrames
import OAI.AlgebraicGeometry.Comparison.Betti.Module.PullbackLocalFrames
import OAI.AlgebraicGeometry.Comparison.Betti.Module.PullbackExistence
import OAI.AlgebraicGeometry.Comparison.Betti.OpensInverseImageLimits

/-! # Analytification Open Frames -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.AnalytificationOpenFrames

noncomputable section

/-! Actual algebraic standard smooth open frames give frames for the original analytified differential modules. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

instance holomorphicOverSite_continuous (U : X.left.Opens) :
    (Over.post (X := U) (Opens.map (Analytification.Base.analytificationMap X))).IsContinuous
      ((Opens.grothendieckTopology X.left).over U)
      ((Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)).over (Open.AffineIsoEvaluation.analyticOpen X U)) :=
  OpensInverseImageLimits.RingedModules.opensMap_overPost_continuous (Analytification.Base.analytificationMap X) U

def holomorphicOverStructureMap (U : X.left.Opens) :
    X.left.ringCatSheaf.over U ⟶
      ((Over.post (X := U) (Opens.map (Analytification.Base.analytificationMap X))).sheafPushforwardContinuous RingCat
        ((Opens.grothendieckTopology X.left).over U)
        ((Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)).over (Open.AffineIsoEvaluation.analyticOpen X U))).obj
          ((StructureMorphism.analyticHolomorphicStructureSheaf X).over (Open.AffineIsoEvaluation.analyticOpen X U)) :=
  @OverRingedMorphism.Modules.overStructureMap (Opens X.left) (Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    inferInstance inferInstance (Opens.grothendieckTopology X.left)
    (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Opens.map (Analytification.Base.analytificationMap X))
    (StructureMorphism.holomorphicAnalytificationSite_continuous X) X.left.ringCatSheaf
    (StructureMorphism.analyticHolomorphicStructureSheaf X) (StructureMorphism.algebraicToHolomorphicStructureSheaf X) U
    (holomorphicOverSite_continuous X U)

abbrev holomorphicOverModuleDirectImage (U : X.left.Opens) :
    SheafOfModules.{0} ((StructureMorphism.analyticHolomorphicStructureSheaf X).over (Open.AffineIsoEvaluation.analyticOpen X U)) ⥤
      SheafOfModules.{0} (X.left.ringCatSheaf.over U) :=
  SheafOfModules.pushforward (F := Over.post (X := U) (Opens.map (Analytification.Base.analytificationMap X)))
    (holomorphicOverStructureMap X U)

instance holomorphicOverModulePushforward_isRightAdjoint (U : X.left.Opens) :
    (holomorphicOverModuleDirectImage X U).IsRightAdjoint :=
  @Module.PullbackExistence.RingedModules.smallModulePushforward_isRightAdjoint
    (Over U) (Over (Open.AffineIsoEvaluation.analyticOpen X U)) inferInstance inferInstance
    ((Opens.grothendieckTopology X.left).over U)
    ((Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)).over (Open.AffineIsoEvaluation.analyticOpen X U))
    (Over.post (X := U) (Opens.map (Analytification.Base.analytificationMap X)))
    (holomorphicOverSite_continuous X U) (X.left.ringCatSheaf.over U)
    ((StructureMorphism.analyticHolomorphicStructureSheaf X).over (Open.AffineIsoEvaluation.analyticOpen X U))
    inferInstance inferInstance (holomorphicOverStructureMap X U)

def analytifiedStandardSmoothOpenFreeIso (U : X.left.Opens)
    [IsAffine (Open.AffineIsoEvaluation.openOver X U).left]
    [Algebra.IsStandardSmooth ℂ (Affine.ExteriorRestrictions.globalCoordinateAlgebra (Open.AffineIsoEvaluation.openOver X U))] (n : ℕ) :
    SheafOfModules.free (R := (StructureMorphism.analyticHolomorphicStructureSheaf X).over (Open.AffineIsoEvaluation.analyticOpen X U))
        (Betti.Smooth.ExteriorFrames.exteriorFrameIndex (Open.AffineIsoEvaluation.openOver X U) n) ≅
      ((StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n)).over
        (Open.AffineIsoEvaluation.analyticOpen X U) := by
  exact @Module.PullbackLocalFrames.RingedModules.modulePullbackOverFreeIso
    (Opens X.left) (Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) inferInstance inferInstance
    inferInstance inferInstance (Opens.grothendieckTopology X.left)
    (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Opens.map (Analytification.Base.analytificationMap X))
    (StructureMorphism.holomorphicAnalytificationSite_continuous X) X.left.ringCatSheaf
    (StructureMorphism.analyticHolomorphicStructureSheaf X) (StructureMorphism.algebraicToHolomorphicStructureSheaf X) U
    (holomorphicOverSite_continuous X U)
    (fun V => OpensInverseImageLimits.RingedModules.opensMap_prodComparison_isIso (Analytification.Base.analytificationMap X) U V)
    (StructureMorphism.holomorphicModuleDirectImage_isRightAdjoint X)
    (holomorphicOverModulePushforward_isRightAdjoint X U)
    inferInstance inferInstance inferInstance inferInstance
    (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n) (Betti.Smooth.ExteriorFrames.exteriorFrameIndex (Open.AffineIsoEvaluation.openOver X U) n)
      (Betti.Smooth.ExteriorFrames.standardSmoothOpenFrameIso X U n)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.AnalytificationOpenFrames
