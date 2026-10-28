import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.SectionProjections

/-! # Pair Section Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PairSectionFrames

noncomputable section

/-! Reindexed products of generating sections cover, and their pulled-back
frame coordinates are the products of the two factor coordinates. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} (L M : Line.Bundles.LineBundle X)

theorem frameCoordinate_pullback_tensorProduct
    (f : Y ⟶ X) (s u : Line.Bundles.structureModule X ⟶ L.sheaf) (t v : Line.Bundles.structureModule X ⟶ M.sheaf)
    [IsIso (Ample.LineBundles.pullbackSection f s)] [IsIso (Ample.LineBundles.pullbackSection f t)] :
    letI : IsIso (Ample.LineBundles.pullbackSection f (ProductSections.tensorProductSection s t)) :=
      (SectionNonvanishing.tensorProductSection_pullback_isIso_iff f L M s t).mpr ⟨inferInstance, inferInstance⟩
    Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection f (ProductSections.tensorProductSection s t))
      (Ample.LineBundles.pullbackSection f (ProductSections.tensorProductSection u v)) =
    Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection f s) (Ample.LineBundles.pullbackSection f u) *
      Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection f t) (Ample.LineBundles.pullbackSection f v) := by
  let : IsIso (PullbackComparison.tensorPullbackComparison f L.sheaf M.sheaf) :=
    LineBundle.TensorBaseChange.lineBundle_tensorPullbackComparison_isIso f L M
  let : IsIso (Ample.LineBundles.pullbackSection f (ProductSections.tensorProductSection s t)) :=
    (SectionNonvanishing.tensorProductSection_pullback_isIso_iff f L M s t).mpr ⟨inferInstance, inferInstance⟩
  let e := asIso (PullbackComparison.tensorPullbackComparison f L.sheaf M.sheaf)
  exact (Frame.FrameRestriction.frameCoordinate_targetIso _ _ e).symm.trans
    ((Frame.FrameRestriction.frameCoordinate_congr (SectionBaseChange.tensorPullbackComparison_section f s t)
      (SectionBaseChange.tensorPullbackComparison_section f u v)).trans
        (SectionCoordinates.frameCoordinate_tensorProduct (Ample.LineBundles.pullbackSection f s) (Ample.LineBundles.pullbackSection f u)
          (Ample.LineBundles.pullbackSection f t) (Ample.LineBundles.pullbackSection f v)))

variable {n m d : ℕ}
variable (e : Segre.ChartProjections.SegreProjectiveIndex.{u} n m ≃ Fin (d + 1))
variable (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
variable (t : Fin (m + 1) → (Line.Bundles.structureModule X ⟶ M.sheaf))

def tensorPairSectionFamily (i : Fin (d + 1)) : Line.Bundles.structureModule X ⟶ (L.tensor M).sheaf :=
  ProductSections.tensorProductSection (s (e.symm i).1.down) (t (e.symm i).2.down)

theorem tensorPairSectionFamily_nonvanishing (i : Fin (d + 1)) :
    Ample.LineBundles.sectionNonvanishing (tensorPairSectionFamily L M e s t i) =
      Ample.LineBundles.sectionNonvanishing (s (e.symm i).1.down) ⊓ Ample.LineBundles.sectionNonvanishing (t (e.symm i).2.down) :=
  SectionNonvanishing.sectionNonvanishing_tensorProduct L M _ _

theorem tensorPairSectionFamily_covers
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ht : ∀ x : X, ∃ j, x ∈ Ample.LineBundles.sectionNonvanishing (t j)) :
    ∀ x : X, ∃ k, x ∈ Ample.LineBundles.sectionNonvanishing (tensorPairSectionFamily L M e s t k) := by
  intro x
  obtain ⟨i, hi⟩ := hs x
  obtain ⟨j, hj⟩ := ht x
  refine ⟨e (ULift.up i, ULift.up j), ?_⟩
  rw [tensorPairSectionFamily_nonvanishing, e.symm_apply_apply]
  exact ⟨hi, hj⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PairSectionFrames
