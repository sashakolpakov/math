import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.RelativeFamilyRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.UniversalBaseChange

/-! # Generated Universal Classification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.GeneratedUniversalClassification

noncomputable section

/-! The generated universal family uniquely classifies smooth relative Hilbert families on arbitrary tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem generatedUniversalFamily_existsUnique_smooth
    {S : Scheme.{u}} {T : Over S} {n B N : ℕ} {P : Polynomial ℚ}
    (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P) [Smooth F.family.scheme.hom]
    (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N) (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B)
    (htest : Truncated.PolynomialTest.truncatedHilbertTestBound n N ≤ B) (hr : Generated.RankTests.GeneratedHilbertRankTest n P N) :
    ∃! g : T ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N,
      (Generated.ParameterFamilies.generatedParameterHilbertFamily (𝟙 _) hflat htest hr).pullback g.left = F := by
  have he : ∀ g : T ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N,
      (Generated.ParameterFamilies.generatedParameterHilbertFamily (𝟙 _) hflat htest hr).pullback g.left =
        Generated.ParameterFamilies.generatedParameterHilbertFamily g.left hflat htest hr := by
    intro g
    simpa only [Category.comp_id] using Hilbert.UniversalBaseChange.generatedParameterHilbertFamily_comp hflat htest hr (𝟙 _) g.left
  obtain ⟨g, hg, hunique⟩ := F.existsUnique_smoothParameterFamily hN hflat htest hr
  exact ⟨g, (he g).trans hg, fun x hx => hunique x ((he x).symm.trans hx)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.GeneratedUniversalClassification
