import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.FrameGluing
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.SectionHyperplaneFrameMatch

/-! # Section Hyperplane Pullback -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.SectionHyperplanePullback

noncomputable section

/-! The actual hyperplane bundle pulls back to the line bundle whose
generating sections define the projective morphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace Cohomology

universe u

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.FrameGluing.PolarizationEmbedding

variable {X S : Scheme.{u}} {M : X.Modules} {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_sectionHyperplane_pullback_iso (f : X ⟶ S)
    (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M))
    (hs : ∀ x : X, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)) (j : Fin (n + 1)) :
    Nonempty ((Scheme.Modules.pullback (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)).obj
      (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := Γ(S, ⊤)) j) ≅ M) :=
  PELModuli.IntegralModel.Section.FrameGluing.PolarizationEmbedding.exists_iso_of_section_transitions (X := X) (ι := ULift.{u} (Fin (n + 1))) M
    ((Scheme.Modules.pullback (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)).obj
      (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := Γ(S, ⊤)) j))
    (fun i => s i.down) (fun i => SectionProjectiveCover.Cohomology.sectionChartPreimage f s hs i.down)
    (by simpa only [iSup_ulift] using SectionProjectiveCover.Cohomology.sectionChartPreimages_cover f s hs)
    (fun i => SectionProjectiveCover.Cohomology.sectionChartPreimage_le f s hs i.down)
    (fun i k => SectionProjectiveCover.Cohomology.sectionOverlapPreimage f s hs i.down k.down)
    (fun i k => SectionProjectiveCover.Cohomology.sectionOverlapPreimage_le_left f s hs i.down k.down)
    (fun i k => SectionProjectiveCover.Cohomology.sectionOverlapPreimage_le_right f s hs i.down k.down)
    (fun i k => SectionProjectiveCover.Cohomology.sectionOverlapPreimage_contains f s hs i.down k.down)
    (fun i => HyperplanePullbackFrames.Cohomology.hyperplanePullbackFrame (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) j i.down)
    (fun i k => SectionHyperplaneFrameMatch.Cohomology.sectionHyperplaneFrame_match f s hs j i.down k.down)

end Cohomology

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.SectionHyperplanePullback
