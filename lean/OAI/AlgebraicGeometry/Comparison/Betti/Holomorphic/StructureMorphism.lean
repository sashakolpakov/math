import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.RegularSections
import OAI.AlgebraicGeometry.Comparison.Betti.ManifoldHolomorphicModuleSheaf
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-! # Structure Morphism -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StructureMorphism

noncomputable section

/-! The actual analytification point map, equipped with actual regular-to-holomorphic evaluation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

instance holomorphicAnalytificationSite_continuous :
    (Opens.map (Analytification.Base.analytificationMap X)).IsContinuous (Opens.grothendieckTopology X.left)
      (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) := by
  apply Functor.isContinuous_of_coverPreserving
  · exact compatiblePreserving_opens_map (Analytification.Base.analytificationMap X)
  · exact coverPreserving_opens_map (Analytification.Base.analytificationMap X)

variable [IsIntegral X.left] [Smooth X.hom]

abbrev analyticHolomorphicStructureSheaf :
    Sheaf (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) RingCat.{0} :=
  ManifoldHolomorphicModuleSheaf.manifoldHolomorphicStructureSheaf (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)

abbrev holomorphicStructureDirectImage : Sheaf (Opens.grothendieckTopology X.left) RingCat.{0} :=
  (TopCat.Sheaf.pushforward RingCat (Analytification.Base.analytificationMap X)).obj (analyticHolomorphicStructureSheaf X)

def algebraicToHolomorphicStructureSheaf : X.left.ringCatSheaf ⟶ holomorphicStructureDirectImage X where
  hom :=
    { app := fun U => RingCat.ofHom (RegularSections.regularHolomorphicSectionMap X U.unop).toRingHom
      naturality := by
        intro U V f
        apply RingCat.hom_ext
        apply RingHom.ext
        intro s
        apply ContMDiffMap.ext
        intro p
        exact Open.AffineIsoEvaluation.sectionEvaluationOn_restrict X (leOfHom f.unop) s p }

theorem algebraicToHolomorphicStructureSheaf_apply (U : X.left.Opens) (s : Γ(X.left, U)) :
    (algebraicToHolomorphicStructureSheaf X).hom.app (op U) s = RegularSections.regularHolomorphicSectionMap X U s := rfl

def holomorphicModuleDirectImage :
    SheafOfModules.{0} (analyticHolomorphicStructureSheaf X) ⥤ SheafOfModules.{0} X.left.ringCatSheaf :=
  SheafOfModules.pushforward (F := Opens.map (Analytification.Base.analytificationMap X))
    (algebraicToHolomorphicStructureSheaf X)

abbrev holomorphicModulePresheafDirectImage :
    PresheafOfModules.{0} (analyticHolomorphicStructureSheaf X).obj ⥤
      PresheafOfModules.{0} X.left.ringCatSheaf.obj :=
  PresheafOfModules.pushforward (F := Opens.map (Analytification.Base.analytificationMap X))
    (algebraicToHolomorphicStructureSheaf X).hom

instance holomorphicModulePresheafDirectImage_isRightAdjoint :
    (holomorphicModulePresheafDirectImage X).IsRightAdjoint := by
  apply CategoryTheory.Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
  exact PresheafOfModules.pullbackObjIsDefined_eq_top
    (F := Opens.map (Analytification.Base.analytificationMap X)) (algebraicToHolomorphicStructureSheaf X).hom

instance holomorphicModuleDirectImage_isRightAdjoint : (holomorphicModuleDirectImage X).IsRightAdjoint := by
  exact (@SheafOfModules.PullbackConstruction.adjunction.{0}
    (Opens X.left) inferInstance (Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) inferInstance
    (Opens.grothendieckTopology X.left)
    (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (Opens.map (Analytification.Base.analytificationMap X)) X.left.ringCatSheaf (analyticHolomorphicStructureSheaf X)
    (holomorphicAnalytificationSite_continuous X) (algebraicToHolomorphicStructureSheaf X)
    (holomorphicModulePresheafDirectImage_isRightAdjoint X) inferInstance inferInstance).isRightAdjoint

def algebraicModuleHolomorphicAnalytification :
    SheafOfModules.{0} X.left.ringCatSheaf ⥤ SheafOfModules.{0} (analyticHolomorphicStructureSheaf X) :=
  (holomorphicModuleDirectImage X).leftAdjoint

def holomorphicModuleAnalytificationAdjunction :
    algebraicModuleHolomorphicAnalytification X ⊣ holomorphicModuleDirectImage X :=
  Adjunction.ofIsRightAdjoint (holomorphicModuleDirectImage X)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StructureMorphism
