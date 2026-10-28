import OAI.AlgebraicGeometry.Comparison.Betti.Open.HolomorphicFrameUnit
import OAI.AlgebraicGeometry.Comparison.Betti.Open.FrameGeneratorRestriction

/-! # Frame Generator Restriction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FrameGeneratorRestriction

noncomputable section

section

/-! The normalized generators of actual analytified open frames commute with
the original restriction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem holomorphicAnalytificationOpenUnitIso_generator_restrict {U V : X.left.Opens}
    (hVU : V ≤ U) (M : SheafOfModules.{0} X.left.ringCatSheaf)
    (e : M.over U ≅ SheafOfModules.unit (X.left.ringCatSheaf.over U)) :
    ((StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.map (homOfLE (Open.SmoothForms.analyticOpen_mono X hVU)).op
        ((Analytification.OpenTrivialization.holomorphicAnalytificationOpenUnitIso X U M e).inv.val.app
          (op (Over.mk (𝟙 (Open.AffineIsoEvaluation.analyticOpen X U))))
          (1 : (StructureMorphism.analyticHolomorphicStructureSheaf X).obj.obj (op (Open.AffineIsoEvaluation.analyticOpen X U)))) =
      (Analytification.OpenTrivialization.holomorphicAnalytificationOpenUnitIso X V M
        (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.left.ringCatSheaf M U e
          (Over.mk (homOfLE hVU)))).inv.val.app (op (Over.mk (𝟙 (Open.AffineIsoEvaluation.analyticOpen X V))))
        (1 : (StructureMorphism.analyticHolomorphicStructureSheaf X).obj.obj (op (Open.AffineIsoEvaluation.analyticOpen X V))) := by
  let eV := SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.left.ringCatSheaf M U e
    (Over.mk (homOfLE hVU))
  have hu := Open.HolomorphicFrameUnit.holomorphicAnalytificationOpenUnitIso_generator X U M e
  have hv := Open.HolomorphicFrameUnit.holomorphicAnalytificationOpenUnitIso_generator X V M eV
  have ha := Open.FrameGeneratorRestriction.RingedModules.overFrameGenerator_restrict X.left.ringCatSheaf M (homOfLE hVU) e
  have hn := PresheafOfModules.naturality_apply
    ((StructureMorphism.holomorphicModuleAnalytificationAdjunction X).unit.app M).val (homOfLE hVU).op
    (Open.FrameGeneratorRestriction.RingedModules.overFrameGenerator X.left.ringCatSheaf M U e)
  exact (congrArg (fun a : ((StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.obj
      (op (Open.AffineIsoEvaluation.analyticOpen X U)) => ((StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.map
        (homOfLE (Open.SmoothForms.analyticOpen_mono X hVU)).op a) hu).trans
      (hn.symm.trans ((congrArg (fun m : M.val.obj (op V) =>
        ((StructureMorphism.holomorphicModuleAnalytificationAdjunction X).unit.app M).val.app (op V) m) ha.symm).trans hv.symm))

end

/-! Original module analytification and original open restrictions commute in
the scalar coordinates of every algebraic line frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem holomorphicAnalytificationOpenUnitIso_section_restrict {U V : X.left.Opens}
    (hVU : V ≤ U) (M : SheafOfModules.{0} X.left.ringCatSheaf)
    (e : M.over U ≅ SheafOfModules.unit (X.left.ringCatSheaf.over U))
    (a : ((StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.obj (op (Open.AffineIsoEvaluation.analyticOpen X U))) :
    Open.UnitFrame.Dolbeault.openUnitFrameSectionEquiv _ _ _
        (Analytification.OpenTrivialization.holomorphicAnalytificationOpenUnitIso X V M
          (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.left.ringCatSheaf M U e
            (Over.mk (homOfLE hVU))))
        (((StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.map
          (homOfLE (Open.SmoothForms.analyticOpen_mono X hVU)).op a) =
      (StructureMorphism.analyticHolomorphicStructureSheaf X).obj.map (homOfLE (Open.SmoothForms.analyticOpen_mono X hVU)).op
        (Open.UnitFrame.Dolbeault.openUnitFrameSectionEquiv _ _ _ (Analytification.OpenTrivialization.holomorphicAnalytificationOpenUnitIso X U M e) a) := by
  exact FrameGeneratorCoordinates.RingedModules.linearFrame_restrict
    ((StructureMorphism.analyticHolomorphicStructureSheaf X).obj.map (homOfLE (Open.SmoothForms.analyticOpen_mono X hVU)).op).hom
    (((StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.restrictₛₗ
      (homOfLE (Open.SmoothForms.analyticOpen_mono X hVU)).op)
    (Open.UnitFrame.Dolbeault.openUnitFrameSectionEquiv _ _ _ (Analytification.OpenTrivialization.holomorphicAnalytificationOpenUnitIso X U M e))
    (Open.UnitFrame.Dolbeault.openUnitFrameSectionEquiv _ _ _ (Analytification.OpenTrivialization.holomorphicAnalytificationOpenUnitIso X V M
      (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.left.ringCatSheaf M U e
        (Over.mk (homOfLE hVU)))))
    (holomorphicAnalytificationOpenUnitIso_generator_restrict X hVU M e) a

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FrameGeneratorRestriction
