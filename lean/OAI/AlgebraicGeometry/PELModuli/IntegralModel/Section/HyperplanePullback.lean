import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.FrameGluing
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.HyperplaneFrameMatch

/-! # Hyperplane Pullback -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.HyperplanePullback

noncomputable section

/-! The actual hyperplane bundle pulls back to the line bundle whose
generating sections define the projective morphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace PolarizationEmbedding

variable {X S : Scheme.{0}} {M : X.Modules} {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_sectionHyperplane_pullback_iso (f : X ⟶ S)
    (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M))
    (hs : ∀ x : X, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)) (j : Fin (n + 1)) :
    Nonempty ((Scheme.Modules.pullback (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)).obj
      (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := Γ(S, ⊤)) j) ≅ M) :=
  FrameGluing.PolarizationEmbedding.exists_iso_of_section_transitions (X := X) (ι := Fin (n + 1)) M
    ((Scheme.Modules.pullback (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)).obj
      (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := Γ(S, ⊤)) j))
    s (ProjectiveCover.PolarizationEmbedding.sectionChartPreimage f s hs) (ProjectiveCover.PolarizationEmbedding.sectionChartPreimages_cover f s hs)
    (ProjectiveCover.PolarizationEmbedding.sectionChartPreimage_le f s hs) (ProjectiveCover.PolarizationEmbedding.sectionOverlapPreimage f s hs)
    (ProjectiveCover.PolarizationEmbedding.sectionOverlapPreimage_le_left f s hs) (ProjectiveCover.PolarizationEmbedding.sectionOverlapPreimage_le_right f s hs)
    (ProjectiveCover.PolarizationEmbedding.sectionOverlapPreimage_contains f s hs)
    (HyperplanePullbackFrames.PolarizationEmbedding.hyperplanePullbackFrame (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) j)
    (HyperplaneFrameMatch.PolarizationEmbedding.sectionHyperplaneFrame_match f s hs j)

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.HyperplanePullback
