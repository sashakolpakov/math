import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Frames
import Mathlib.AlgebraicGeometry.Fiber

/-! # Point Base Section Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.PointBaseSectionFrames

noncomputable section

/-! A section of a line bundle is a frame if it becomes one under a surjective map. Over a one-point base, checking the residue fiber suffices, including for nonreduced bases. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem lineBundle_section_isIso_of_surjective_pullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : Function.Surjective f) (L : Line.Bundles.LineBundle Y)
    (s : Line.Bundles.structureModule Y ⟶ L.sheaf) [IsIso (Ample.LineBundles.pullbackSection f s)] : IsIso s := by
  have h : Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s) = ⊤ :=
    (Section.Frames.isIso_iff_sectionNonvanishing_eq_top _).mp inferInstance
  rw [LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange f L s] at h
  apply (Section.Frames.isIso_iff_sectionNonvanishing_eq_top s).mpr
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := hf y
  have hx : x ∈ f ⁻¹ᵁ Ample.LineBundles.sectionNonvanishing s := h.symm ▸ (show x ∈ (⊤ : X.Opens) from trivial)
  exact hx

theorem fiberInclusion_surjective_of_subsingleton_base
    {X S : Scheme.{u}} [Subsingleton S] (f : X ⟶ S) (x : S) :
    Function.Surjective (f.fiberι x) := by
  intro y
  have hy : y ∈ f ⁻¹' {x} := Subsingleton.elim (f y) x
  rw [← f.range_fiberι x] at hy
  exact hy

theorem lineBundle_section_isIso_of_single_fiber_frame
    {X S : Scheme.{u}} [Subsingleton S] (f : X ⟶ S) (x : S)
    (L : Line.Bundles.LineBundle X) (s : Line.Bundles.structureModule X ⟶ L.sheaf)
    [IsIso (Ample.LineBundles.pullbackSection (f.fiberι x) s)] : IsIso s :=
  lineBundle_section_isIso_of_surjective_pullback (f.fiberι x)
    (fiberInclusion_surjective_of_subsingleton_base f x) L s

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.PointBaseSectionFrames
