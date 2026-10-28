import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LocalNormRefinement
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormRankBasis

/-! # Global Norm Section -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GlobalNormSection.Construction

noncomputable section

/-! The norm of a section of the pulled-back line is an actual global
section of the line power given by the finite-flat degree. Its
nonvanishing locus records nonvanishing on the entire fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X Y : Scheme.{u}} (q : X ⟶ Y)
  [IsFinite q] [Flat q] [LocallyOfFinitePresentation q]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (d : ℕ) (hdegree : ∀ y : Y, q.finrank y = d)
  (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.pullback q).sheaf)

include hdegree in
theorem existsUnique_globalNormSection :
    ∃! a : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ (L.tensorPower d).sheaf,
      ∀ U : LocalNormSections.Construction.NormFrameOpen q L d, AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.openSet.ι a = LocalNormSections.Construction.localNormSection U z := by
  exact OpenSectionGluing.Construction.existsUnique_section_of_basis_refinements
    (fun U : LocalNormSections.Construction.NormFrameOpen q L d => U.openSet)
    (NormFrameBasis.Construction.normFrameOpens_isBasis (NormRankBasis.Construction.normFrameOpens_cover_of_finrank q L d hdegree))
    (fun U => LocalNormSections.Construction.localNormSection U z) (fun V U h => LocalNormRefinement.Construction.localNormSection_refine q L d V U h z)

def finiteFlatNormSection : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ (L.tensorPower d).sheaf :=
  (existsUnique_globalNormSection q L d hdegree z).choose

theorem finiteFlatNormSection_restrict (U : LocalNormSections.Construction.NormFrameOpen q L d) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.openSet.ι (finiteFlatNormSection q L d hdegree z) = LocalNormSections.Construction.localNormSection U z :=
  (existsUnique_globalNormSection q L d hdegree z).choose_spec.1 U

theorem finiteFlatNormSection_mem_nonvanishing (y : Y) :
    y ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (finiteFlatNormSection q L d hdegree z) ↔
      ∀ x : X, q x = y → x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z := by
  obtain ⟨U, hy⟩ := NormRankBasis.Construction.normFrameOpens_cover_of_finrank q L d hdegree y
  have hD : U.openSet.ι ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (finiteFlatNormSection q L d hdegree z) =
      AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (LocalNormSections.Construction.localNormSection U z) :=
    (AbelianModuli.HilbertConstruction.Section.Nonvanishing.sectionNonvanishing_pullback U.openSet.ι (finiteFlatNormSection q L d hdegree z)).symm.trans
      (congrArg AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (finiteFlatNormSection_restrict q L d hdegree z U))
  exact (congrArg (fun V : U.openSet.toScheme.Opens => (⟨y, hy⟩ : U.openSet.toScheme) ∈ V) hD).to_iff.trans
    (LocalNormSections.Construction.localNormSection_mem_nonvanishing U z ⟨y, hy⟩)

theorem finiteFlatNormSection_nonvanishing :
    (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (finiteFlatNormSection q L d hdegree z) : Set Y) =
      (q '' (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z : Set X)ᶜ)ᶜ := by
  ext y
  change y ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (finiteFlatNormSection q L d hdegree z) ↔ _
  rw [finiteFlatNormSection_mem_nonvanishing]
  simp only [Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
  exact ⟨fun h x hx hxy => hx (h x hxy), fun h x hxy => by
    by_contra hx
    exact h x hx hxy⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GlobalNormSection.Construction
