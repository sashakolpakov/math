import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ExtensionCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.CofaceCoordinates

/-! # Line Module -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.LineModule

noncomputable section

/-! The actual algebraic module sheaf of coordinates satisfying
the prescribed regular transition equations is a kernel sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable {X : Scheme.{0}} {I : Type} (U : I → X.Opens)
    (r : ∀ i : Fin 2 → I, Γ(X, ExtensionCoordinates.cechIntersection U 1 i))

def cechLineEquations : TermModules.cechTermModule X U 0 ⟶ TermModules.cechTermModule X U 1 :=
  ModuleDifferential.cechModuleCoface X U 0 0 - ModuleDifferential.cechModuleCoface X U 0 1 ≫ ExtensionCoordinates.cechCoefficientMultiplication U 1 r

def cechLineModule : X.Modules := kernel (cechLineEquations U r)

def cechLineModuleInclusion : cechLineModule U r ⟶ TermModules.cechTermModule X U 0 :=
  kernel.ι (cechLineEquations U r)

theorem cechLineModule_relation :
    cechLineModuleInclusion U r ≫ ModuleDifferential.cechModuleCoface X U 0 0 =
      cechLineModuleInclusion U r ≫ ModuleDifferential.cechModuleCoface X U 0 1 ≫ ExtensionCoordinates.cechCoefficientMultiplication U 1 r := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub]
  exact kernel.condition (cechLineEquations U r)

theorem cechLineModule_section_relation (W : X.Opens) (m : Γ(cechLineModule U r, W))
    (i : Fin 2 → I) :
    X.presheaf.map (homOfLE (inf_le_inf_left W (ExtensionCoordinates.cechIntersection_le_face U 0 0 i))).op
      (ExtensionCoordinates.cechCoefficient U 0 W ((cechLineModuleInclusion U r).app W m) (ExtensionCoordinates.cechFaceIndex 0 0 i)) =
      X.presheaf.map (homOfLE (show W ⊓ ExtensionCoordinates.cechIntersection U 1 i ≤ ExtensionCoordinates.cechIntersection U 1 i
        from inf_le_right)).op (r i) *
        X.presheaf.map (homOfLE (inf_le_inf_left W (ExtensionCoordinates.cechIntersection_le_face U 0 1 i))).op
          (ExtensionCoordinates.cechCoefficient U 0 W ((cechLineModuleInclusion U r).app W m) (ExtensionCoordinates.cechFaceIndex 0 1 i)) := by
  have h := congrArg (fun f => ExtensionCoordinates.cechCoefficient U 1 W (f.app W m) i) (cechLineModule_relation U r)
  change ExtensionCoordinates.cechCoefficient U 1 W
      ((ModuleDifferential.cechModuleCoface X U 0 0).app W ((cechLineModuleInclusion U r).app W m)) i =
    ExtensionCoordinates.cechCoefficient U 1 W (ExtensionCoordinates.cechMultiplySections U 1 r W
      ((ModuleDifferential.cechModuleCoface X U 0 1).app W ((cechLineModuleInclusion U r).app W m))) i at h
  rw [CofaceCoordinates.cechCoefficient_coface, ExtensionCoordinates.cechMultiplySections_coefficient, CofaceCoordinates.cechCoefficient_coface] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.LineModule
