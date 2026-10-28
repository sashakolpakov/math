import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.CoordinateSections

/-! # Global Coordinate Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GlobalCoordinateValues

noncomputable section

/-! The local generator coefficient of a global frame section is its prescribed chart coordinate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : Transitions.OpenFrameTransitions U)

theorem openFrameSection_app_one_coordinate
    (s : Line.Bundles.structureModule X ⟶ ModuleSheaf.openFrameModuleSheaf D) (k : ι)
    (V : X.Opens) (hV : V ≤ U k) :
    s.app V (1 : Γ(X, V)) = SectionGenerators.openFrameGenerator D V k hV
      (X.presheaf.map (homOfLE hV).op
        (show Γ(X, U k) from CoefficientSections.openFrameGlobalTupleMap D
          (Global.Sections.moduleSectionHomEquiv (ModuleSheaf.openFrameModuleSheaf D) s) k)) := by
  let z : SectionModules.openFrameSectionModule U D ⊤ := Global.Sections.moduleSectionHomEquiv (ModuleSheaf.openFrameModuleSheaf D) s
  have hv : s.app V (1 : Γ(X, V)) = (ModuleSheaf.openFrameModuleSheaf D).presheaf.map (homOfLE le_top).op z := by
    have h := Global.SectionMapValues.moduleSectionHomEquiv_symm_app (ModuleSheaf.openFrameModuleSheaf D) z V 1
    rw [show (Global.Sections.moduleSectionHomEquiv (ModuleSheaf.openFrameModuleSheaf D)).symm z = s from
      (Global.Sections.moduleSectionHomEquiv (ModuleSheaf.openFrameModuleSheaf D)).symm_apply_apply s, one_smul] at h
    exact h
  rw [hv]
  change RestrictionCompatibility.openFrameSectionRestriction D (show V ≤ ⊤ from le_top) z = _
  apply CoordinateSections.openFrameSection_coordinate_injective D V k hV
  let r : Γ(X, U k) := CoefficientSections.openFrameGlobalTupleMap D z k
  change X.presheaf.map (homOfLE (inf_le_inf le_top (le_refl (U k)))).op (z.val k) =
    D.frameValues V k hV (X.presheaf.map (homOfLE hV).op r) k
  rw [D.frameValues_self]
  exact (Relative.OpenFunctionUnits.openFunction_restriction_comp (le_inf le_top (le_refl (U k)))
    (show V ⊓ U k ≤ U k from inf_le_right) (z.val k)).symm.trans
      (Relative.OpenFunctionUnits.openFunction_restriction_comp hV (show V ⊓ U k ≤ V from inf_le_left) r).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GlobalCoordinateValues
