import OAI.AlgebraicGeometry.SheafCohomology.Projective.AffineScalarSectionCover
import OAI.AlgebraicGeometry.SheafCohomology.Projective.EpiSectionFamily
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.Frames

/-! # Line Bundle Section Cover -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.LineBundleSectionCover

noncomputable section

/-! A finite epimorphism from structure sheaves to a line bundle gives an actual frame cover. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem lineBundle_epi_sections_cover {X : Scheme.{u}} {ι : Type} [Fintype ι]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (s : ι → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf)) [Epi (Sigma.desc s)] :
    ∀ x : X, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i) := by
  intro x
  obtain ⟨U, hx, hU, ⟨e⟩⟩ := L.exists_affine_frame x
  have : IsAffine U.toScheme := hU
  let F := Scheme.Modules.pullback U.ι
  have : Epi (Sigma.desc (fun i => F.map (s i))) :=
    EpiSectionFamily.epi_sigmaDesc_map F (fun _ : ι => AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) s
  let t : ι → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme ⟶ F.obj L.sheaf) := fun i => AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι (s i)
  have : Epi (Sigma.desc t) := EpiSectionFamily.epi_sigmaDesc_precomp_iso
    (fun _ : ι => AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) (fun _ : ι => F.obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X))
    (fun _ => (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso U.ι).symm) (fun i => F.map (s i))
  let r : ι → End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) := fun i => t i ≫ e.hom
  have : Epi (Sigma.desc r) := EpiSectionFamily.epi_sigmaDesc_postcomp_iso
    (fun _ : ι => AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) t e
  obtain ⟨i, hi⟩ := AffineScalarSectionCover.affine_scalar_sections_cover r (⟨x, hx⟩ : U.toScheme)
  change (⟨x, hx⟩ : U.toScheme) ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (t i ≫ e.hom) at hi
  rw [AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso] at hi
  change (⟨x, hx⟩ : U.toScheme) ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι (s i)) at hi
  rw [AbelianModuli.HilbertConstruction.Section.Nonvanishing.sectionNonvanishing_pullback] at hi
  exact ⟨i, hi⟩

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.LineBundleSectionCover
