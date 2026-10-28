import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ScalarSectionCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.GlobalModuleGenerators
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.Frames

/-! # Line Bundle Section Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Finite global generators of a line bundle give an actual frame cover. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem Generated.LineBundleSectionCover.lineBundle_epi_sections_cover {X : Scheme.{u}} {ι : Type u} [Fintype ι]
    (L : Line.Bundles.LineBundle X) (s : ι → (Line.Bundles.structureModule X ⟶ L.sheaf)) [Epi (Sigma.desc s)] :
    ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i) := by
  intro x
  obtain ⟨U, hx, hU, ⟨e⟩⟩ := L.exists_affine_frame x
  have : IsAffine U.toScheme := hU
  let F := Scheme.Modules.pullback U.ι
  have : Epi (Sigma.desc (fun i => F.map (s i))) :=
    EpimorphicCoproductFamilies.epi_sigmaDesc_map F (fun _ : ι => Line.Bundles.structureModule X) s
  let t : ι → (Line.Bundles.structureModule U.toScheme ⟶ F.obj L.sheaf) := fun i => Ample.LineBundles.pullbackSection U.ι (s i)
  have : Epi (Sigma.desc t) := EpimorphicCoproductFamilies.epi_sigmaDesc_precomp_iso
    (fun _ : ι => Line.Bundles.structureModule U.toScheme) (fun _ : ι => F.obj (Line.Bundles.structureModule X))
    (fun _ => (Line.Bundles.structureModulePullbackIso U.ι).symm) (fun i => F.map (s i))
  let r : ι → End (Line.Bundles.structureModule U.toScheme) := fun i => t i ≫ e.hom
  have : Epi (Sigma.desc r) := EpimorphicCoproductFamilies.epi_sigmaDesc_postcomp_iso
    (fun _ : ι => Line.Bundles.structureModule U.toScheme) t e
  obtain ⟨i, hi⟩ := Affine.ScalarSectionCover.affine_scalar_sections_cover r (⟨x, hx⟩ : U.toScheme)
  change (⟨x, hx⟩ : U.toScheme) ∈ Ample.LineBundles.sectionNonvanishing (t i ≫ e.hom) at hi
  rw [Ample.Powers.sectionNonvanishing_comp_iso] at hi
  change (⟨x, hx⟩ : U.toScheme) ∈ Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection U.ι (s i)) at hi
  rw [Section.Nonvanishing.sectionNonvanishing_pullback] at hi
  exact ⟨i, hi⟩

theorem Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators.lineBundle_section_cover {X : Scheme.{u}}
    (L : Line.Bundles.LineBundle X) (hL : HilbertConstruction.Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators L.sheaf) :
    ∃ (ι : Type u) (_ : Finite ι) (s : ι → (Line.Bundles.structureModule X ⟶ L.sheaf)),
      ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i) := by
  obtain ⟨ι, hι, s, hs⟩ := hL
  let : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  let : Epi (Sigma.desc s) := hs
  exact ⟨ι, hι, s, Generated.LineBundleSectionCover.lineBundle_epi_sections_cover L s⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
