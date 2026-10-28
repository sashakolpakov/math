import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ProjectiveTransitions

/-! # Projective Cover -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ProjectiveCover

noncomputable section

/-! Native projective chart preimages and overlaps of a section family. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace PolarizationEmbedding

variable {X S : Scheme.{0}} {M : X.Modules} {n : ℕ} (f : X ⟶ S)
  (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M))
  (hs : ∀ x : X, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
attribute [local instance] MvPolynomial.gradedAlgebra

def sectionChartPreimage (i : Fin (n + 1)) : X.Opens :=
  AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs ⁻¹ᵁ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := Γ(S, ⊤)) i

def sectionOverlapPreimage (i k : Fin (n + 1)) : X.Opens :=
  AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs ⁻¹ᵁ SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := Γ(S, ⊤)) i k

theorem sectionChartPreimage_le (i : Fin (n + 1)) :
    sectionChartPreimage f s hs i ≤ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i) :=
  (AbelianModuli.HilbertConstruction.ProjectiveChart.Preimages.sectionAbsoluteMorphism_preimage f s hs i).le

theorem sectionChartPreimages_cover : iSup (sectionChartPreimage f s hs) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨i, hi⟩ := hs x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i,
    (congrArg (fun Z : X.Opens => x ∈ Z) (AbelianModuli.HilbertConstruction.ProjectiveChart.Preimages.sectionAbsoluteMorphism_preimage f s hs i)).mpr hi⟩

theorem sectionOverlapPreimage_le_left (i k : Fin (n + 1)) :
    sectionOverlapPreimage f s hs i k ≤ sectionChartPreimage f s hs i :=
  (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs).preimage_mono (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left i k)

theorem sectionOverlapPreimage_le_right (i k : Fin (n + 1)) :
    sectionOverlapPreimage f s hs i k ≤ sectionChartPreimage f s hs k :=
  (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs).preimage_mono (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right i k)

theorem sectionOverlapPreimage_contains (i k : Fin (n + 1)) :
    sectionChartPreimage f s hs i ⊓ sectionChartPreimage f s hs k ≤
      sectionOverlapPreimage f s hs i k :=
  (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs).preimage_mono (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_eq i k).ge

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ProjectiveCover
