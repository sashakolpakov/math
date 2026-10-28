import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionFrames

/-! # Section Nonvanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionNonvanishing

noncomputable section

/-! The nonvanishing open of a tensor product section is the intersection of the two factor opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem tensorProductSection_pullback_isIso_iff (f : X ⟶ Y) (L M : Line.Bundles.LineBundle Y)
    (s : Line.Bundles.structureModule Y ⟶ L.sheaf) (t : Line.Bundles.structureModule Y ⟶ M.sheaf) :
    IsIso (Ample.LineBundles.pullbackSection f (ProductSections.tensorProductSection s t)) ↔
      IsIso (Ample.LineBundles.pullbackSection f s) ∧ IsIso (Ample.LineBundles.pullbackSection f t) := by
  let : IsIso (PullbackComparison.tensorPullbackComparison f L.sheaf M.sheaf) :=
    LineBundle.TensorBaseChange.lineBundle_tensorPullbackComparison_isIso f L M
  exact (isIso_comp_right_iff (Ample.LineBundles.pullbackSection f (ProductSections.tensorProductSection s t))
    (PullbackComparison.tensorPullbackComparison f L.sheaf M.sheaf)).symm.trans
      (((congrArg IsIso (SectionBaseChange.tensorPullbackComparison_section f s t)).to_iff).trans
        (SectionFrames.tensorProductSection_isIso_iff (L.pullback f) (M.pullback f) _ _))

theorem sectionNonvanishing_tensorProduct (L M : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (t : Line.Bundles.structureModule X ⟶ M.sheaf) :
    Ample.LineBundles.sectionNonvanishing (ProductSections.tensorProductSection s t) = Ample.LineBundles.sectionNonvanishing s ⊓ Ample.LineBundles.sectionNonvanishing t := by
  apply le_antisymm
  · have h := (tensorProductSection_pullback_isIso_iff
      (Ample.LineBundles.sectionNonvanishing (ProductSections.tensorProductSection s t)).ι L M s t).mp inferInstance
    exact le_inf (le_sSup h.1) (le_sSup h.2)
  · let W := Ample.LineBundles.sectionNonvanishing s ⊓ Ample.LineBundles.sectionNonvanishing t
    have hs : IsIso (Ample.LineBundles.pullbackSection W.ι s) := by
      apply (Section.Frames.isIso_iff_sectionNonvanishing_eq_top _).mpr
      rw [Section.Nonvanishing.sectionNonvanishing_pullback]
      ext x
      exact iff_true_intro x.property.1
    have ht : IsIso (Ample.LineBundles.pullbackSection W.ι t) := by
      apply (Section.Frames.isIso_iff_sectionNonvanishing_eq_top _).mpr
      rw [Section.Nonvanishing.sectionNonvanishing_pullback]
      ext x
      exact iff_true_intro x.property.2
    exact le_sSup ((tensorProductSection_pullback_isIso_iff W.ι L M s t).mpr ⟨hs, ht⟩)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionNonvanishing
