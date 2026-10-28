import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.CoefficientSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.FromOpenFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.SectionRestriction

/-! # Coordinate Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.CoordinateSections

noncomputable section

/-! A compatible global frame tuple gives an actual section, with its local value determined by one coordinate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : Transitions.OpenFrameTransitions U)

theorem openFrameSection_coordinate_injective (V : X.Opens) (k : ι) (hV : V ≤ U k) :
    Function.Injective (fun z : SectionModules.openFrameSectionModule U D V => z.val k) := by
  intro z w h
  obtain ⟨a, rfl⟩ := LocalFreeness.openFrameGenerator_surjective D V k hV z
  obtain ⟨b, rfl⟩ := LocalFreeness.openFrameGenerator_surjective D V k hV w
  have hab : a = b :=
    (LocalFreeness.openFunctionRestriction_bijective_of_eq inf_le_left (inf_eq_left.mpr hV)).injective
      ((D.frameValues_self V k hV a).symm.trans (h.trans (D.frameValues_self V k hV b)))
  exact congrArg (SectionGenerators.openFrameGenerator D V k hV) hab

def openFrameSectionOfCompatible (x : GlobalTuples.OpenFrameGlobalTuple U) (hx : Frame.TransitionEquations.FrameCompatible D x) :
    Line.Bundles.structureModule X ⟶ ModuleSheaf.openFrameModuleSheaf D :=
  (Global.Sections.moduleSectionHomEquiv (ModuleSheaf.openFrameModuleSheaf D)).symm
    ((GlobalSections.openFrameGlobalSectionsEquiv D).symm
      ⟨x, (GlobalCompatibility.openFrameGlobalCompatibleModule_mem D x).mpr hx⟩)

theorem openFrameSectionOfCompatible_tuple (x : GlobalTuples.OpenFrameGlobalTuple U) (hx : Frame.TransitionEquations.FrameCompatible D x) :
    CoefficientSections.openFrameGlobalTupleMap D
      (Global.Sections.moduleSectionHomEquiv (ModuleSheaf.openFrameModuleSheaf D) (openFrameSectionOfCompatible D x hx)) = x := by
  let y : GlobalCompatibility.openFrameGlobalCompatibleModule D :=
    ⟨x, (GlobalCompatibility.openFrameGlobalCompatibleModule_mem D x).mpr hx⟩
  have h : Global.Sections.moduleSectionHomEquiv (ModuleSheaf.openFrameModuleSheaf D) (openFrameSectionOfCompatible D x hx) =
      (show Γ(ModuleSheaf.openFrameModuleSheaf D, ⊤) from (GlobalSections.openFrameGlobalSectionsEquiv D).symm y) :=
    (Global.Sections.moduleSectionHomEquiv (ModuleSheaf.openFrameModuleSheaf D)).apply_symm_apply _
  exact (congrArg (fun z : Γ(ModuleSheaf.openFrameModuleSheaf D, ⊤) => CoefficientSections.openFrameGlobalTupleMap D z) h).trans
    (congrArg Subtype.val ((GlobalSections.openFrameGlobalSectionsEquiv D).apply_symm_apply y))

theorem openFrameSection_app_one_of_coordinate_one
    (s : Line.Bundles.structureModule X ⟶ ModuleSheaf.openFrameModuleSheaf D) (k : ι)
    (hk : (show Γ(X, U k) from CoefficientSections.openFrameGlobalTupleMap D
      (Global.Sections.moduleSectionHomEquiv (ModuleSheaf.openFrameModuleSheaf D) s) k) = 1)
    (V : X.Opens) (hV : V ≤ U k) :
    s.app V (1 : Γ(X, V)) = SectionGenerators.openFrameGenerator D V k hV 1 := by
  let z : SectionModules.openFrameSectionModule U D ⊤ := Global.Sections.moduleSectionHomEquiv (ModuleSheaf.openFrameModuleSheaf D) s
  have hv : s.app V (1 : Γ(X, V)) = (ModuleSheaf.openFrameModuleSheaf D).presheaf.map (homOfLE le_top).op z := by
    have h := Global.SectionMapValues.moduleSectionHomEquiv_symm_app (ModuleSheaf.openFrameModuleSheaf D) z V 1
    rw [show (Global.Sections.moduleSectionHomEquiv (ModuleSheaf.openFrameModuleSheaf D)).symm z = s from
      (Global.Sections.moduleSectionHomEquiv (ModuleSheaf.openFrameModuleSheaf D)).symm_apply_apply s, one_smul] at h
    exact h
  rw [hv]
  change RestrictionCompatibility.openFrameSectionRestriction D (show V ≤ ⊤ from le_top) z =
    SectionGenerators.openFrameGenerator D V k hV 1
  apply openFrameSection_coordinate_injective D V k hV
  change X.presheaf.map (homOfLE (inf_le_inf le_top (le_refl (U k)))).op (z.val k) =
    D.frameValues V k hV 1 k
  rw [D.frameValues_self, map_one]
  have h := congrArg (X.presheaf.map (homOfLE (show V ⊓ U k ≤ U k from inf_le_right)).op) hk
  rw [map_one] at h
  change X.presheaf.map (homOfLE (show V ⊓ U k ≤ U k from inf_le_right)).op
    (X.presheaf.map (homOfLE (show U k ≤ ⊤ ⊓ U k from le_inf le_top le_rfl)).op
      (z.val k)) = 1 at h
  exact (Relative.OpenFunctionUnits.openFunction_restriction_comp (le_inf le_top (le_refl (U k)))
    (show V ⊓ U k ≤ U k from inf_le_right) (z.val k)).symm.trans h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.CoordinateSections
