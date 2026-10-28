import OAI.AlgebraicGeometry.Comparison.Betti.PullbackOpenScalars
import OAI.AlgebraicGeometry.Comparison.Betti.Open.UnitFrame

/-! # Frame Scalars -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FrameScalars

noncomputable section

/-! Actual analytification sends a regular scalar transition between open
frames to multiplication by its original holomorphic evaluation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem holomorphicAnalytificationOpenUnitIso_scalar (U : X.left.Opens)
    (M : SheafOfModules.{0} X.left.ringCatSheaf)
    (e g : M.over U ≅ SheafOfModules.unit (X.left.ringCatSheaf.over U))
    (r : Γ(X.left, U))
    (h : e.hom = g.hom ≫ SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.left.ringCatSheaf U r) :
    (Analytification.OpenTrivialization.holomorphicAnalytificationOpenUnitIso X U M e).hom =
      (Analytification.OpenTrivialization.holomorphicAnalytificationOpenUnitIso X U M g).hom ≫
        SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd (StructureMorphism.analyticHolomorphicStructureSheaf X) (Open.AffineIsoEvaluation.analyticOpen X U)
          (RegularSections.regularHolomorphicSectionMap X U r) := by
  exact @PullbackOpenScalars.RingedModules.modulePullbackOverUnitIso_scalar
    (Opens X.left) (Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) inferInstance inferInstance
    (Opens.grothendieckTopology X.left) (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (Opens.map (Analytification.Base.analytificationMap X)) (StructureMorphism.holomorphicAnalytificationSite_continuous X)
    X.left.ringCatSheaf (StructureMorphism.analyticHolomorphicStructureSheaf X)
    (StructureMorphism.algebraicToHolomorphicStructureSheaf X) U (AnalytificationOpenFrames.holomorphicOverSite_continuous X U)
    (AnalytificationOpenFrames.holomorphicOverModulePushforward_isRightAdjoint X U) inferInstance inferInstance
    (fun V => OpensInverseImageLimits.RingedModules.opensMap_prodComparison_isIso (Analytification.Base.analytificationMap X) U V)
    (StructureMorphism.holomorphicModuleDirectImage_isRightAdjoint X) M e g r h

theorem holomorphicAnalytificationFrameSection_scalar (U : X.left.Opens)
    (M : SheafOfModules.{0} X.left.ringCatSheaf)
    (e g : M.over U ≅ SheafOfModules.unit (X.left.ringCatSheaf.over U))
    (r : Γ(X.left, U))
    (h : e.hom = g.hom ≫ SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.left.ringCatSheaf U r)
    (a : ((StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.obj
      (op (Open.AffineIsoEvaluation.analyticOpen X U))) :
    Open.UnitFrame.Dolbeault.openUnitFrameSectionEquiv _ _ _
        (Analytification.OpenTrivialization.holomorphicAnalytificationOpenUnitIso X U M e) a =
      Mul.mul (α := (StructureMorphism.analyticHolomorphicStructureSheaf X).obj.obj (op (Open.AffineIsoEvaluation.analyticOpen X U)))
        (Open.UnitFrame.Dolbeault.openUnitFrameSectionEquiv _ _ _
          (Analytification.OpenTrivialization.holomorphicAnalytificationOpenUnitIso X U M g) a)
        (RegularSections.regularHolomorphicSectionMap X U r) := by
  let T : (Over (Open.AffineIsoEvaluation.analyticOpen X U))ᵒᵖ := op (Over.mk (𝟙 (Open.AffineIsoEvaluation.analyticOpen X U)))
  have hs := congrArg (fun f => f.val.app T)
    (holomorphicAnalytificationOpenUnitIso_scalar X U M e g r h)
  have ha := ConcreteCategory.congr_hom hs a
  change _ = (SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd (StructureMorphism.analyticHolomorphicStructureSheaf X) (Open.AffineIsoEvaluation.analyticOpen X U)
    (RegularSections.regularHolomorphicSectionMap X U r)).val.app T
      ((Analytification.OpenTrivialization.holomorphicAnalytificationOpenUnitIso X U M g).hom.val.app T a) at ha
  erw [SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd_app_apply] at ha
  have hr : (StructureMorphism.analyticHolomorphicStructureSheaf X).obj.map (𝟙 (op (Open.AffineIsoEvaluation.analyticOpen X U)))
      (RegularSections.regularHolomorphicSectionMap X U r) = RegularSections.regularHolomorphicSectionMap X U r :=
    ConcreteCategory.congr_hom ((StructureMorphism.analyticHolomorphicStructureSheaf X).obj.map_id _) _
  exact ha.trans (congrArg (fun b : (StructureMorphism.analyticHolomorphicStructureSheaf X).obj.obj
      (op (Open.AffineIsoEvaluation.analyticOpen X U)) => Mul.mul (α := (StructureMorphism.analyticHolomorphicStructureSheaf X).obj.obj
        (op (Open.AffineIsoEvaluation.analyticOpen X U)))
          (Open.UnitFrame.Dolbeault.openUnitFrameSectionEquiv _ _ _
            (Analytification.OpenTrivialization.holomorphicAnalytificationOpenUnitIso X U M g) a) b) hr)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FrameScalars
