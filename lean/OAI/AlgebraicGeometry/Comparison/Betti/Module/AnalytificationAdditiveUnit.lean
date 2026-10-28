import OAI.AlgebraicGeometry.Comparison.Betti.Open.HolomorphicFrameUnit
import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechImage

/-! # Analytification Additive Unit -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Module.AnalytificationAdditiveUnit

noncomputable section

/-! Forgetting scalars in the original analytification unit gives its actual additive presheaf map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def moduleAnalytificationAdditiveUnit (M : SheafOfModules.{0} X.left.ringCatSheaf) :
    M.val.presheaf ⟶ (Opens.map (Analytification.Base.analytificationMap X)).op ⋙
      ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf :=
  ((SheafOfModules.toSheaf X.left.ringCatSheaf).map
    ((Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction X).unit.app M)).hom

theorem moduleAnalytificationAdditiveUnit_app (M : SheafOfModules.{0} X.left.ringCatSheaf)
    (U : X.left.Opens) (m : M.val.obj (op U)) :
    (moduleAnalytificationAdditiveUnit X M).app (op U) m =
      ((Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction X).unit.app M).val.app (op U) m := rfl

theorem moduleAnalytificationAdditiveUnit_frame (U : X.left.Opens)
    (M : SheafOfModules.{0} X.left.ringCatSheaf)
    (e : M.over U ≅ SheafOfModules.unit (X.left.ringCatSheaf.over U))
    (m : M.val.obj (op U)) :
    (Analytification.OpenTrivialization.holomorphicAnalytificationOpenUnitIso X U M e).hom.val.app (op (Over.mk (𝟙 (Open.AffineIsoEvaluation.analyticOpen X U))))
      ((moduleAnalytificationAdditiveUnit X M).app (op U) m) =
        Holomorphic.RegularSections.regularHolomorphicSectionMap X U (e.hom.val.app (op (Over.mk (𝟙 U))) m) :=
  Open.HolomorphicFrameUnit.holomorphicAnalytificationOpenUnitIso_section_unit X U M e m

end

end OAI.AlgebraicGeometry.Comparison.Betti.Module.AnalytificationAdditiveUnit
