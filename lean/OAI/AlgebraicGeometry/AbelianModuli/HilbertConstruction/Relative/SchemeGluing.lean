import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-! # Scheme Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.SchemeGluing

noncomputable section

/-! Open gluing data in schemes over a fixed base have a glued scheme over that base. Its underlying scheme is the ordinary scheme gluing, and its chart maps are an open cover. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} (D : CategoryTheory.GlueData.{u} (Over S))
variable (hD : ∀ i j, IsOpenImmersion (D.f i j).left)

def relativeSchemeGlueData : Scheme.GlueData where
  toGlueData := D.mapGlueData (Over.forget S)
  f_open := hD

include hD in
theorem relativeGlueData_forget_hasColimit : HasColimit (D.diagram.multispan ⋙ Over.forget S) := by
  have hcol : HasColimit (D.mapGlueData (Over.forget S)).diagram.multispan :=
    inferInstanceAs (HasColimit (relativeSchemeGlueData D hD).toGlueData.diagram.multispan)
  exact @hasColimit_of_iso _ _ _ _ _ _ hcol (D.diagramIso (Over.forget S))

include hD in
theorem relativeGlueData_hasColimit : HasMulticoequalizer D.diagram := by
  have : HasColimit (D.diagram.multispan ⋙ Over.forget S) := relativeGlueData_forget_hasColimit D hD
  exact Over.hasColimit_of_hasColimit_comp_forget D.diagram.multispan

def relativeGlued : Over S := by
  have : HasMulticoequalizer D.diagram := relativeGlueData_hasColimit D hD
  exact D.glued

def relativeGlueComparison : (relativeGlued D hD).left ≅ (relativeSchemeGlueData D hD).glued :=
  by
    have : HasMulticoequalizer D.diagram := relativeGlueData_hasColimit D hD
    have : HasColimit (D.diagram.multispan ⋙ Over.forget S) := relativeGlueData_forget_hasColimit D hD
    exact D.gluedIso (Over.forget S)

def relativeGlueInclusion (i : D.J) : D.U i ⟶ relativeGlued D hD := by
  have : HasMulticoequalizer D.diagram := relativeGlueData_hasColimit D hD
  exact D.ι i

theorem relativeGlueInclusion_comparison (i : D.J) :
    (relativeGlueInclusion D hD i).left ≫ (relativeGlueComparison D hD).hom =
      (relativeSchemeGlueData D hD).ι i :=
  by
    have : HasMulticoequalizer D.diagram := relativeGlueData_hasColimit D hD
    have : HasColimit (D.diagram.multispan ⋙ Over.forget S) := relativeGlueData_forget_hasColimit D hD
    exact D.ι_gluedIso_hom (Over.forget S) i

theorem relativeGlueInclusion_open (i : D.J) :
    IsOpenImmersion (relativeGlueInclusion D hD i).left := by
  have : HasMulticoequalizer D.diagram := relativeGlueData_hasColimit D hD
  have : HasColimit (D.diagram.multispan ⋙ Over.forget S) := relativeGlueData_forget_hasColimit D hD
  have he : (relativeGlueInclusion D hD i).left =
      (relativeSchemeGlueData D hD).ι i ≫ (relativeGlueComparison D hD).inv :=
    (D.ι_gluedIso_inv (Over.forget S) i).symm
  rw [he]
  exact MorphismProperty.comp_mem IsOpenImmersion _ _
    (Scheme.GlueData.ι_isOpenImmersion (relativeSchemeGlueData D hD) i) inferInstance

theorem relativeGlueInclusion_covers (x : (relativeGlued D hD).left) :
    ∃ i y, (relativeGlueInclusion D hD i).left y = x := by
  obtain ⟨i, y, hy⟩ := (relativeSchemeGlueData D hD).ι_jointly_surjective
    ((relativeGlueComparison D hD).hom x)
  refine ⟨i, y, ?_⟩
  apply (TopCat.homeoOfIso ((Scheme.forgetToTop).mapIso (relativeGlueComparison D hD))).injective
  exact (congrArg (fun k : (D.U i).left ⟶ (relativeSchemeGlueData D hD).glued => k y)
    (relativeGlueInclusion_comparison D hD i)).trans hy

def relativeGlueOpenCover : Scheme.OpenCover (relativeGlued D hD).left := by
  have (i : D.J) : IsOpenImmersion (relativeGlueInclusion D hD i).left := relativeGlueInclusion_open D hD i
  exact Scheme.Cover.mkOfCovers D.J (fun i => (D.U i).left)
    (fun i => (relativeGlueInclusion D hD i).left) (relativeGlueInclusion_covers D hD)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.SchemeGluing
