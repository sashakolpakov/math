import OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleEpiCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Frames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.FrameRestriction

/-! # Section Cover Epi -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.SectionCoverEpi

noncomputable section

/-! Sections that are frames on a covering family generate the actual module sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem module_epi_of_sections_cover {X : Scheme.{u}} {ι : Type} (M : X.Modules)
    (s : ι → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M))
    (hs : ∀ x : X, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)) : Epi (Sigma.desc s) := by
  let U := fun i => AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)
  have hU : ⨆ i, U i = ⊤ := by
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr (hs x)
  apply ModuleEpiCover.Scheme.Modules.epi_of_restrictFunctor_map_epi_of_iSup_eq_top U hU
  intro i
  let F := Scheme.Modules.restrictFunctor (U i).ι
  have : IsIso (F.map (s i)) := (AbelianModuli.HilbertConstruction.Power.Nonvanishing.isIso_restrict_map_iff (U i).ι (s i)).mpr
    ((AbelianModuli.HilbertConstruction.Section.Nonvanishing.isIso_pullbackSection_iff (U i).ι (s i)).mp inferInstance)
  exact epi_of_epi_fac (show F.map (Sigma.ι (fun _ : ι => AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) i) ≫
    F.map (Sigma.desc s) = F.map (s i) by rw [← F.map_comp, Sigma.ι_comp_desc])

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.SectionCoverEpi
