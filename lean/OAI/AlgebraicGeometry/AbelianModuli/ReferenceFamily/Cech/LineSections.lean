import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.LineModule
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ModuleKernelSections

/-! # Line Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.LineSections

noncomputable section

/-! Solutions of the original regular transition equations lift
uniquely to sections of the actual kernel sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.TopCat.Sheaf

variable {X : Scheme.{0}} {I : Type} (U : I → X.Opens)
    (r : ∀ i : Fin 2 → I, Γ(X, ExtensionCoordinates.cechIntersection U 1 i))

def CechLineCompatible (W : X.Opens) (a : Γ(TermModules.cechTermModule X U 0, W)) : Prop :=
  ∀ i : Fin 2 → I,
    X.presheaf.map (homOfLE (inf_le_inf_left W (ExtensionCoordinates.cechIntersection_le_face U 0 0 i))).op
      (ExtensionCoordinates.cechCoefficient U 0 W a (ExtensionCoordinates.cechFaceIndex 0 0 i)) =
      X.presheaf.map (homOfLE (show W ⊓ ExtensionCoordinates.cechIntersection U 1 i ≤ ExtensionCoordinates.cechIntersection U 1 i
        from inf_le_right)).op (r i) *
        X.presheaf.map (homOfLE (inf_le_inf_left W (ExtensionCoordinates.cechIntersection_le_face U 0 1 i))).op
          (ExtensionCoordinates.cechCoefficient U 0 W a (ExtensionCoordinates.cechFaceIndex 0 1 i))

theorem cechLineEquations_zero_iff (W : X.Opens) (a : Γ(TermModules.cechTermModule X U 0, W)) :
    (LineModule.cechLineEquations U r).app W a = 0 ↔ CechLineCompatible U r W a := by
  change (ModuleDifferential.cechModuleCoface X U 0 0).app W a -
    ExtensionCoordinates.cechMultiplySections U 1 r W ((ModuleDifferential.cechModuleCoface X U 0 1).app W a) = 0 ↔ _
  rw [sub_eq_zero]
  constructor
  · intro h i
    have hi := congrArg (fun b => ExtensionCoordinates.cechCoefficient U 1 W b i) h
    rw [CofaceCoordinates.cechCoefficient_coface, ExtensionCoordinates.cechMultiplySections_coefficient, CofaceCoordinates.cechCoefficient_coface] at hi
    exact hi
  · intro h
    apply (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv (TermModules.structureAbelianSheaf X) U 1 W).injective
    funext i
    change ExtensionCoordinates.cechCoefficient U 1 W _ i = ExtensionCoordinates.cechCoefficient U 1 W _ i
    rw [CofaceCoordinates.cechCoefficient_coface, ExtensionCoordinates.cechMultiplySections_coefficient, CofaceCoordinates.cechCoefficient_coface]
    exact h i

def cechLineSectionLift (W : X.Opens) (a : Γ(TermModules.cechTermModule X U 0, W))
    (h : CechLineCompatible U r W a) : Γ(LineModule.cechLineModule U r, W) :=
  ModuleKernelSections.moduleKernelSectionLift (LineModule.cechLineEquations U r) W a ((cechLineEquations_zero_iff U r W a).mpr h)

theorem cechLineSectionLift_inclusion (W : X.Opens) (a : Γ(TermModules.cechTermModule X U 0, W))
    (h : CechLineCompatible U r W a) :
    (LineModule.cechLineModuleInclusion U r).app W (cechLineSectionLift U r W a h) = a :=
  ModuleKernelSections.moduleKernelSectionLift_inclusion (LineModule.cechLineEquations U r) W a _

theorem cechLineModule_sections_injective (W : X.Opens) :
    Function.Injective ((LineModule.cechLineModuleInclusion U r).app W) :=
  ModuleKernelSections.moduleKernel_inclusion_injective (LineModule.cechLineEquations U r) W

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.LineSections
