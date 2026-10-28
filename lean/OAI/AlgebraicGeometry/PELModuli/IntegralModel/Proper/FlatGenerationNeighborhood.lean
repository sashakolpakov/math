import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.FiberSectionLifts
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.SpanGeneration
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.GenerationNeighborhood

/-! # Flat Generation Neighborhood -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.FlatGenerationNeighborhood

noncomputable section

/-! Actual fiber section lifting and properness construct a neighborhood
on which a finite family of global sections generates the line bundle. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.GenerationNeighborhood.PolarizationEmbedding

theorem properFlat_exists_generating_sections_near_fiber
    {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (x : S)
    [Subsingleton (SheafCohomology.AffineH.Projective.H ((Scheme.Modules.pullback (f.fiberι x)).obj L.sheaf) 1)]
    (hgen : ∀ y : f.fiber x, ∃ s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (f.fiber x) ⟶
      (L.pullback (f.fiberι x)).sheaf, y ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) :
    ∃ (n : ℕ) (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf))
      (U : S.Opens), x ∈ U ∧ IsAffineOpen U ∧
        ∀ y : (f ⁻¹ᵁ U).toScheme, ∃ i, y ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing
          (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (f ⁻¹ᵁ U).ι (s i)) := by
  obtain ⟨n, v, hv⟩ := Finite.FiberSectionLifts.properFlat_exists_finite_fiber_section_lifts f L x
  let s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf) :=
    Fin.lastCases 0 (fun i => (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).symm (v i))
  have hfib : ∀ y : f.fiber x, ∃ i, y ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing
      (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (f.fiberι x) (s i)) := by
    intro y
    obtain ⟨i, hi⟩ := Section.SpanGeneration.pulled_section_family_covers_of_span (f.fiberι x)
      (f.fiberToSpecResidueField x) L v hv hgen y
    exact ⟨i.castSucc, by simpa only [s, Fin.lastCases_castSucc] using hi⟩
  have hx : x ∈ Section.GenerationNeighborhood.PolarizationEmbedding.sectionGenerationOpen f L s := by
    apply (Section.GenerationNeighborhood.PolarizationEmbedding.mem_sectionGenerationOpen f L s x).mpr
    intro y hy
    have hr : y ∈ Set.range (f.fiberι x) := by
      rw [f.range_fiberι x]
      exact hy
    obtain ⟨z, rfl⟩ := hr
    obtain ⟨i, hi⟩ := hfib z
    refine ⟨i, ?_⟩
    rw [AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange _ L] at hi
    exact hi
  obtain ⟨U, hU, hxU, hsub⟩ := exists_isAffineOpen_mem_and_subset hx
  refine ⟨n, s, U, hxU, hU, ?_⟩
  intro y
  obtain ⟨i, hi⟩ := (Section.GenerationNeighborhood.PolarizationEmbedding.mem_sectionGenerationOpen f L s (f y.val)).mp
    (hsub y.property) y.val rfl
  refine ⟨i, ?_⟩
  rw [AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange _ L]
  exact hi

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.FlatGenerationNeighborhood
