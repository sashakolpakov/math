import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.ModulePresheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.TupleSheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.SectionLocality

/-! # Module Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.ModuleSheaf

noncomputable section

/-! Compatible frame coordinates form an actual sheaf of modules, proved by unique gluing in the regular-function coordinate sheaf and locality of the transition equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : Transitions.OpenFrameTransitions U)

def openFrameSectionTypePresheaf : TopCat.Presheaf (Type u) X :=
  (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj (ModulePresheaf.openFrameModulePresheaf D) ⋙ forget AddCommGrpCat

theorem openFrameSectionTypePresheaf_isSheaf : (openFrameSectionTypePresheaf D).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types _).mpr
  intro α V s hs
  change ∀ a b, RestrictionCompatibility.openFrameSectionRestriction D (show V a ⊓ V b ≤ V a from inf_le_left) (s a) =
    RestrictionCompatibility.openFrameSectionRestriction D (show V a ⊓ V b ≤ V b from inf_le_right) (s b) at hs
  have hvals : (TupleSheaf.openFrameTuplePresheaf U).IsCompatible V (fun a => (s a).val) := by
    intro a b
    exact congrArg Subtype.val (hs a b)
  obtain ⟨t, ht, hu⟩ := (TupleSheaf.openFrameTuplePresheaf_isSheaf U).isSheafUniqueGluing_types (fun a => (s a).val) hvals
  have htmem : t ∈ SectionModules.openFrameSectionModule U D (iSup V) :=
    SectionLocality.openFrameSectionModule_mem_of_locally D V (fun a => le_iSup V a) le_rfl t
      (fun a => (ht a).symm ▸ (s a).property)
  refine ⟨⟨t, htmem⟩, ?_, ?_⟩
  · intro a
    exact Subtype.ext (ht a)
  · intro q hq
    apply Subtype.ext
    exact hu q.val (fun a => congrArg Subtype.val (hq a))

def openFrameModuleSheaf : X.Modules where
  val := ModulePresheaf.openFrameModulePresheaf D
  isSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp' (forget AddCommGrpCat) _).mpr
    (openFrameSectionTypePresheaf_isSheaf D)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.ModuleSheaf
