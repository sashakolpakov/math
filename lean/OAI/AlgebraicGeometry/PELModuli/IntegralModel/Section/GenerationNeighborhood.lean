import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange

/-! # Generation Neighborhood -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.GenerationNeighborhood.PolarizationEmbedding

noncomputable section

/-! Sections generating one fiber generate the family over an actual
open neighborhood. Properness excludes their common zero locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange
universe u v
variable {X S : Scheme.{u}} (p : X ⟶ S) [UniversallyClosed p]
variable {I : Type v} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
variable (s : I → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf))

def sectionGenerationOpen : S.Opens :=
  ⟨(p '' (((⨆ i, AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)) : X.Opens) : Set X)ᶜ)ᶜ,
    (p.isClosedMap _ (⨆ i, AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)).isOpen.isClosed_compl).isOpen_compl⟩

theorem mem_sectionGenerationOpen (b : S) :
    b ∈ sectionGenerationOpen p L s ↔
      ∀ x : X, p x = b → ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i) := by
  constructor
  · intro hb x hx
    apply TopologicalSpace.Opens.mem_iSup.mp
    by_contra hn
    exact hb ⟨x, hn, hx⟩
  · intro hb
    rintro ⟨x, hx, hxb⟩
    exact hx (TopologicalSpace.Opens.mem_iSup.mpr (hb x hxb))

theorem sections_cover_over_generationOpen :
    ∀ x : (p ⁻¹ᵁ sectionGenerationOpen p L s).toScheme,
      ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing
        (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (p ⁻¹ᵁ sectionGenerationOpen p L s).ι (s i)) := by
  intro x
  obtain ⟨i, hi⟩ := (mem_sectionGenerationOpen p L s (p x.val)).mp x.property x.val rfl
  refine ⟨i, ?_⟩
  rw [AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange _ L]
  exact hi

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.GenerationNeighborhood.PolarizationEmbedding
