import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ProjectiveCover
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.HyperplanePullbackFrames

/-! # Hyperplane Frame Match -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.HyperplaneFrameMatch

noncomputable section

/-! Pulled-back projective frames have the original section transition ratios. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace PolarizationEmbedding

variable {X S : Scheme.{0}} {M : X.Modules} {n : ℕ} (f : X ⟶ S)
  (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M))
  (hs : ∀ x : X, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
attribute [local instance] MvPolynomial.gradedAlgebra

theorem sectionHyperplaneFrame_match (j i k : Fin (n + 1)) :
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (ProjectiveCover.PolarizationEmbedding.sectionOverlapPreimage_le_left f s hs i k)
      (HyperplanePullbackFrames.PolarizationEmbedding.hyperplanePullbackFrame (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) j i)).hom =
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (ProjectiveCover.PolarizationEmbedding.sectionOverlapPreimage_le_right f s hs i k)
      (HyperplanePullbackFrames.PolarizationEmbedding.hyperplanePullbackFrame (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) j k)).hom ≫
      SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection
        ((X.homOfLE ((ProjectiveCover.PolarizationEmbedding.sectionOverlapPreimage_le_left f s hs i k).trans
          (ProjectiveCover.PolarizationEmbedding.sectionChartPreimage_le f s hs i))).appTop (AbelianModuli.HilbertConstruction.Section.Frames.sectionRatio (s i) (s k))) := by
  obtain ⟨hi, hr⟩ := ProjectiveTransitions.PolarizationEmbedding.sectionProjective_overlap_unit f s hs i k
  exact (HyperplanePullbackFrames.PolarizationEmbedding.hyperplanePullbackFrame_transition (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) j i k).trans
    (congrArg (fun r =>
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (ProjectiveCover.PolarizationEmbedding.sectionOverlapPreimage_le_right f s hs i k)
        (HyperplanePullbackFrames.PolarizationEmbedding.hyperplanePullbackFrame (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) j k)).hom ≫
          SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection r) hr)

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.HyperplaneFrameMatch
