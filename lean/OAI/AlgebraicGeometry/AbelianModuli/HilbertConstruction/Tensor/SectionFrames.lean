import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionBaseChange

/-! # Section Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionFrames

noncomputable section

/-! A product of two line-bundle sections is a frame exactly when both factors are frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

theorem tensorProductSection_isIso_iff_of_frames {L M : X.Modules}
    (s : Line.Bundles.structureModule X ⟶ L) (t : Line.Bundles.structureModule X ⟶ M)
    (e : L ≅ Line.Bundles.structureModule X) (f : M ≅ Line.Bundles.structureModule X) :
    IsIso (ProductSections.tensorProductSection s t) ↔ IsIso s ∧ IsIso t := by
  constructor
  · intro h
    let := h
    let a : End (Line.Bundles.structureModule X) := s ≫ e.hom
    let b : End (Line.Bundles.structureModule X) := t ≫ f.hom
    have hp : IsIso (ProductSections.tensorProductSection a b) := by
      rw [← ProductSections.tensorProductSection_postcomp]
      infer_instance
    let := hp
    have hab : IsIso (a ≫ b) := by
      rw [← ProductSections.tensorProductSection_unit_formula a b]
      infer_instance
    have hu : IsUnit (Frame.Coordinates.structureModuleEndValue X b * Frame.Coordinates.structureModuleEndValue X a) := by
      rw [← map_mul]
      exact (Global.Sections.structureModuleEnd_isIso_iff (b * a)).mp hab
    obtain ⟨hb, ha⟩ := (Commute.all _ _).isUnit_mul_iff.mp hu
    have ha' : IsIso a := (Global.Sections.structureModuleEnd_isIso_iff a).mpr ha
    have hb' : IsIso b := (Global.Sections.structureModuleEnd_isIso_iff b).mpr hb
    exact ⟨(isIso_comp_right_iff s e.hom).mp ha', (isIso_comp_right_iff t f.hom).mp hb'⟩
  · rintro ⟨hs, ht⟩
    let := hs
    let := ht
    infer_instance

theorem tensorProductSection_isIso_iff (L M : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (t : Line.Bundles.structureModule X ⟶ M.sheaf) :
    IsIso (ProductSections.tensorProductSection s t) ↔ IsIso s ∧ IsIso t := by
  constructor
  · intro h
    let := h
    have hlocal (x : X) : ∃ W : X.Opens, x ∈ W ∧
        IsIso (Ample.LineBundles.pullbackSection W.ι s) ∧ IsIso (Ample.LineBundles.pullbackSection W.ι t) := by
      obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyTrivial x
      obtain ⟨V, hxV, ⟨f⟩⟩ := M.locallyTrivial x
      let W := U ⊓ V
      have hp : IsIso (ProductSections.tensorProductSection (Ample.LineBundles.pullbackSection W.ι s) (Ample.LineBundles.pullbackSection W.ι t)) := by
        rw [← SectionBaseChange.tensorPullbackComparison_section]
        infer_instance
      exact ⟨W, ⟨hxU, hxV⟩,
        (tensorProductSection_isIso_iff_of_frames _ _
          (L.frameRestrict (show W ≤ U from inf_le_left) e)
          (M.frameRestrict (show W ≤ V from inf_le_right) f)).mp hp⟩
    constructor
    · apply Local.ModuleIsomorphisms.moduleMap_isIso_of_locally s
      intro x
      obtain ⟨W, hx, hs, _⟩ := hlocal x
      exact ⟨W, hx, (Section.Nonvanishing.isIso_pullbackSection_iff W.ι s).mp hs⟩
    · apply Local.ModuleIsomorphisms.moduleMap_isIso_of_locally t
      intro x
      obtain ⟨W, hx, _, ht⟩ := hlocal x
      exact ⟨W, hx, (Section.Nonvanishing.isIso_pullbackSection_iff W.ι t).mp ht⟩
  · rintro ⟨hs, ht⟩
    let := hs
    let := ht
    infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionFrames
