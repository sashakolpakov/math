import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmpleSectionEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange

/-! # Section Ampleness -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.SectionAmpleness

noncomputable section

/-! An affine morphism defined by sections supplies the affine
nonvanishing cover in the definition of ampleness. This also works for
the actual pulled-back sections under a further scheme morphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace PolarizationEmbedding
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange
universe u
variable {X S T : Scheme.{u}} (f : X ⟶ S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) {n : ℕ}
variable (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf))
variable (hs : ∀ x : X, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))

theorem isAmple_pullback_of_affine_section_composite (a : T ⟶ X) [CompactSpace T]
    [IsAffineHom (a ≫ AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)] : (L.pullback a).IsAmple := by
  refine ⟨isCompact_univ, fun x => ?_⟩
  obtain ⟨i, hi⟩ := hs (a x)
  refine ⟨1, Nat.zero_lt_one, L.pullback a, AbelianModuli.HilbertConstruction.Tensor.Powers.isTensorPower_one _,
    AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection a (s i), ?_, ?_⟩
  · rw [AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange a L]
    exact hi
  · rw [AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange a L,
      ← AbelianModuli.HilbertConstruction.ProjectiveChart.Preimages.sectionAbsoluteMorphism_preimage f s hs i]
    exact (AbelianModuli.HilbertConstruction.StandardProjectiveCharts.standardProjectiveChart_isAffine Γ(S, ⊤) n i).preimage
      (a ≫ AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)

theorem isAmple_of_affine_section_morphism [CompactSpace X]
    [IsAffineHom (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)] : L.IsAmple := by
  refine ⟨isCompact_univ, fun x => ?_⟩
  obtain ⟨i, hi⟩ := hs x
  refine ⟨1, Nat.zero_lt_one, L, AbelianModuli.HilbertConstruction.Tensor.Powers.isTensorPower_one _, s i, hi, ?_⟩
  rw [← AbelianModuli.HilbertConstruction.ProjectiveChart.Preimages.sectionAbsoluteMorphism_preimage f s hs i]
  exact (AbelianModuli.HilbertConstruction.StandardProjectiveCharts.standardProjectiveChart_isAffine Γ(S, ⊤) n i).preimage
    (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.SectionAmpleness
