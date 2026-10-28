import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionFrameGluing
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FrameCoordinatePullback

/-! # Section Ratio Gluing -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionRatioGluing.Construction

noncomputable section

/-! Covering section ratios determine the underlying line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem lineBundleIso_of_sectionAppCoordinates {X : Scheme.{u}} {M N : X.Modules}
    {ι : Type u} (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (s : ι → (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)) (t : ι → (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N))
    (hs : ∀ i, U i ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (ht : ∀ i, U i ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (t i))
    (h : ∀ i j, FrameCoordinatePullback.Construction.sectionAppCoordinate (s i) (s j) (hs i) =
      FrameCoordinatePullback.Construction.sectionAppCoordinate (t i) (t j) (ht i)) : Nonempty (M ≅ N) := by
  apply SectionFrameGluing.Construction.lineBundleIso_of_section_coordinates U hU s t hs ht
  intro i j V hi _ r
  have hc : FrameCoordinatePullback.Construction.sectionAppCoordinate (s i) (s j) (hi.trans (hs i)) =
      FrameCoordinatePullback.Construction.sectionAppCoordinate (t i) (t j) (hi.trans (ht i)) :=
    (FrameCoordinatePullback.Construction.sectionAppCoordinate_restrict (s i) (s j) hi (hs i)).symm.trans
      ((congrArg (fun z : Γ(X, U i) => X.presheaf.map (homOfLE hi).op z) (h i j)).trans
        (FrameCoordinatePullback.Construction.sectionAppCoordinate_restrict (t i) (t j) hi (ht i)))
  rw [FrameCoordinatePullback.Construction.sectionAppCoordinate_smul, FrameCoordinatePullback.Construction.sectionAppCoordinate_smul, hc]

theorem lineBundleIso_of_local_frameCoordinates {X : Scheme.{u}} {M N : X.Modules}
    {ι : Type u} (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (s : ι → (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)) (t : ι → (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N))
    (hs : ∀ i, U i ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (ht : ∀ i, U i ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (t i))
    (h : ∀ i j,
      letI := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PowerLocus.pullbackSection_isIso_of_le (hs i) (s i)
      letI := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PowerLocus.pullbackSection_isIso_of_le (ht i) (t i)
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (U i).ι (s i)) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (U i).ι (s j)) =
        AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (U i).ι (t i)) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (U i).ι (t j))) :
    Nonempty (M ≅ N) := by
  apply lineBundleIso_of_sectionAppCoordinates U hU s t hs ht
  intro i j
  exact (FrameCoordinatePullback.Construction.sectionAppCoordinate_eq_frameCoordinate (s i) (s j) (hs i)).trans
    ((congrArg (U i).topIso.hom (h i j)).trans
      (FrameCoordinatePullback.Construction.sectionAppCoordinate_eq_frameCoordinate (t i) (t j) (ht i)).symm)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionRatioGluing.Construction
