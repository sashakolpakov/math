import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StructureMorphism
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Limits.IsConnected

/-! # Analytification Unit -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.AnalytificationUnit

noncomputable section

/-! Actual module analytification preserves the unit module, with its canonical evaluation map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace RingedModules

theorem canonicalUnitMap_isIso {C D : Type} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    {S : Sheaf J RingCat.{0}} {R : Sheaf K RingCat.{0}} [F.IsContinuous J K]
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R)
    [(SheafOfModules.pushforward.{0} φ).IsRightAdjoint] [F.Final] :
    IsIso (SheafOfModules.pullbackObjUnitToUnit φ) := by
  infer_instance

end RingedModules

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

instance holomorphicAnalytificationSite_final : (Opens.map (Analytification.Base.analytificationMap X)).Final where
  out U := by
    let T : StructuredArrow U (Opens.map (Analytification.Base.analytificationMap X)) :=
      StructuredArrow.mk (Y := (⊤ : Opens X.left)) (homOfLE le_top)
    have hT : Limits.IsTerminal T := Limits.IsTerminal.ofUniqueHom
      (fun W => StructuredArrow.homMk
        (show W.right ⟶ (⊤ : Opens X.left) from homOfLE le_top))
      (fun _ _ => StructuredArrow.hom_ext _ _ (Subsingleton.elim _ _))
    exact CategoryTheory.isConnected_of_isTerminal _ hT

variable [IsIntegral X.left] [Smooth X.hom]

def holomorphicUnitToDirectImageUnit :
    SheafOfModules.unit X.left.ringCatSheaf ⟶
      (StructureMorphism.holomorphicModuleDirectImage X).obj (SheafOfModules.unit (StructureMorphism.analyticHolomorphicStructureSheaf X)) :=
  @SheafOfModules.unitToPushforwardObjUnit
    (Opens X.left) inferInstance (Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) inferInstance
    (Opens.grothendieckTopology X.left) (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (Opens.map (Analytification.Base.analytificationMap X)) X.left.ringCatSheaf (StructureMorphism.analyticHolomorphicStructureSheaf X)
    (StructureMorphism.holomorphicAnalytificationSite_continuous X) (StructureMorphism.algebraicToHolomorphicStructureSheaf X)

def holomorphicAnalytificationUnitMap :
    (StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj (SheafOfModules.unit X.left.ringCatSheaf) ⟶
      SheafOfModules.unit (StructureMorphism.analyticHolomorphicStructureSheaf X) :=
  @SheafOfModules.pullbackObjUnitToUnit
    (Opens X.left) inferInstance (Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) inferInstance
    (Opens.grothendieckTopology X.left) (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (Opens.map (Analytification.Base.analytificationMap X)) X.left.ringCatSheaf (StructureMorphism.analyticHolomorphicStructureSheaf X)
    (StructureMorphism.holomorphicAnalytificationSite_continuous X) (StructureMorphism.algebraicToHolomorphicStructureSheaf X)
    (StructureMorphism.holomorphicModuleDirectImage_isRightAdjoint X)

instance holomorphicAnalytificationUnitMap_isIso : IsIso (holomorphicAnalytificationUnitMap X) := by
  exact @RingedModules.canonicalUnitMap_isIso
    (Opens X.left) (Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) inferInstance inferInstance
    (Opens.grothendieckTopology X.left) (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (Opens.map (Analytification.Base.analytificationMap X)) X.left.ringCatSheaf (StructureMorphism.analyticHolomorphicStructureSheaf X)
    (StructureMorphism.holomorphicAnalytificationSite_continuous X) (StructureMorphism.algebraicToHolomorphicStructureSheaf X)
    (StructureMorphism.holomorphicModuleDirectImage_isRightAdjoint X) (holomorphicAnalytificationSite_final X)

def holomorphicAnalytificationUnitIso :
    (StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj (SheafOfModules.unit X.left.ringCatSheaf) ≅
      SheafOfModules.unit (StructureMorphism.analyticHolomorphicStructureSheaf X) :=
  asIso (holomorphicAnalytificationUnitMap X)

theorem holomorphicAnalytificationUnitMap_normalization :
    (StructureMorphism.holomorphicModuleAnalytificationAdjunction X).homEquiv _ _
      (holomorphicAnalytificationUnitMap X) = holomorphicUnitToDirectImageUnit X :=
  Equiv.apply_symm_apply _ _

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.AnalytificationUnit
