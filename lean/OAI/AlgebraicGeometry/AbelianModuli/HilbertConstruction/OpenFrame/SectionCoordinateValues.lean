import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.CoordinateSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Gluing

/-! # Section Coordinate Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.SectionCoordinateValues

noncomputable section

/-! On a frame chart, a global section is the local generator multiplied by
its actual chart coefficient. This retains arbitrary coordinate values. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens}

theorem openFrameSection_app_of_tuple (D : Transitions.OpenFrameTransitions U)
    (s : Line.Bundles.structureModule X ⟶ ModuleSheaf.openFrameModuleSheaf D) (k : ι) :
    s.app (U k) (1 : Γ(X, U k)) = SectionGenerators.openFrameGenerator D (U k) k le_rfl
      (CoefficientSections.openFrameGlobalTupleMap D (Global.Sections.moduleSectionHomEquiv (ModuleSheaf.openFrameModuleSheaf D) s) k) := by
  let z : SectionModules.openFrameSectionModule U D ⊤ := Global.Sections.moduleSectionHomEquiv (ModuleSheaf.openFrameModuleSheaf D) s
  rw [← Section.Gluing.moduleSectionHomEquiv_restrict]
  apply CoordinateSections.openFrameSection_coordinate_injective D (U k) k le_rfl
  change X.presheaf.map
      (homOfLE (show U k ⊓ U k ≤ ⊤ ⊓ U k from inf_le_inf le_top le_rfl)).op (z.val k) =
    D.frameValues (U k) k le_rfl
      (X.presheaf.map (homOfLE (show U k ≤ ⊤ ⊓ U k from le_inf le_top le_rfl)).op (z.val k)) k
  rw [D.frameValues_self]
  exact (Relative.OpenFunctionUnits.openFunction_restriction_comp (le_inf le_top (le_refl (U k)))
    (show U k ⊓ U k ≤ U k from inf_le_left) (z.val k)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.SectionCoordinateValues
