import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.AnalytificationOpenFrames
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.AnalytificationUnit

/-! # Open Trivialization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytification.OpenTrivialization

noncomputable section

/-! Actual algebraic line-module trivializations pull back to unit-module
trivializations on the corresponding analytic open slices. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace RingedModules

variable {C D : Type} [SmallCategory C] [SmallCategory D]
  [HasBinaryProducts C] [HasBinaryProducts D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [F.IsContinuous J K]
  {S : Sheaf J RingCat.{0}} {R : Sheaf K RingCat.{0}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R) (U : C)
  [(Over.post (X := U) F).IsContinuous (J.over U) (K.over (F.obj U))]
  [∀ V, IsIso (prodComparison F U V)]
  [(SheafOfModules.pushforward.{0} φ).IsRightAdjoint]
  [(SheafOfModules.pushforward.{0} (OverRingedMorphism.Modules.overStructureMap φ U)).IsRightAdjoint]

def modulePullbackOverUnitIso (M : SheafOfModules.{0} S)
    (e : M.over U ≅ SheafOfModules.unit (S.over U)) :
    ((SheafOfModules.pullback φ).obj M).over (F.obj U) ≅
      SheafOfModules.unit (R.over (F.obj U)) := by
  let : (Over.post (X := U) F).Final := OverPost.RingedModules.overPost_final F U
  have : IsIso (SheafOfModules.pullbackObjUnitToUnit (OverRingedMorphism.Modules.overStructureMap φ U)) :=
    Holomorphic.AnalytificationUnit.RingedModules.canonicalUnitMap_isIso (OverRingedMorphism.Modules.overStructureMap φ U)
  exact (Module.PullbackOver.RingedModules.modulePullbackOverIso φ U).app M ≪≫
    (SheafOfModules.pullback (OverRingedMorphism.Modules.overStructureMap φ U)).mapIso e ≪≫
      asIso (SheafOfModules.pullbackObjUnitToUnit (OverRingedMorphism.Modules.overStructureMap φ U))

end RingedModules

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def holomorphicAnalytificationOpenUnitIso (U : X.left.Opens)
    (M : SheafOfModules.{0} X.left.ringCatSheaf)
    (e : M.over U ≅ SheafOfModules.unit (X.left.ringCatSheaf.over U)) :
    ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).over (Open.AffineIsoEvaluation.analyticOpen X U) ≅
      SheafOfModules.unit ((Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X).over (Open.AffineIsoEvaluation.analyticOpen X U)) := by
  exact @RingedModules.modulePullbackOverUnitIso
    (Opens X.left) (Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) inferInstance inferInstance
    inferInstance inferInstance (Opens.grothendieckTopology X.left)
    (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Opens.map (Base.analytificationMap X))
    (Holomorphic.StructureMorphism.holomorphicAnalytificationSite_continuous X) X.left.ringCatSheaf
    (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X) (Holomorphic.StructureMorphism.algebraicToHolomorphicStructureSheaf X) U
    (Holomorphic.AnalytificationOpenFrames.holomorphicOverSite_continuous X U)
    (fun V => OpensInverseImageLimits.RingedModules.opensMap_prodComparison_isIso (Base.analytificationMap X) U V)
    (Holomorphic.StructureMorphism.holomorphicModuleDirectImage_isRightAdjoint X)
    (Holomorphic.AnalytificationOpenFrames.holomorphicOverModulePushforward_isRightAdjoint X U)
    M e

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytification.OpenTrivialization
