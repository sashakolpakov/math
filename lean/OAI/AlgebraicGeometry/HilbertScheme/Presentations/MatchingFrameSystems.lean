import OAI.AlgebraicGeometry.HilbertScheme.Presentations.OverFrameComparisons
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.ModuleIsoGluing

/-! # Matching Frame Systems -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatchingFrameSystems

noncomputable section

/-! Two systems of local line-bundle frames with equal transition
functions give an actual global isomorphism of the underlying module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem exists_moduleIso_of_matching_frame_transitions {X : Scheme.{u}} (M N : X.Modules)
    {ι : Type v} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (W : ι → ι → X.Opens) (hl : ∀ i j, W i j ≤ U i) (hr : ∀ i j, W i j ≤ U j)
    (hW : ∀ i j, U i ⊓ U j ≤ W i j)
    (e : ∀ i, M.restrict (U i).ι ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (U i).toScheme)
    (f : ∀ i, N.restrict (U i).ι ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (U i).toScheme)
    (ht : ∀ i j,
      FrameTransitionCocycles.frameTransitionValue (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (hl i j) (e i))
        (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (hr i j) (e j)) =
      FrameTransitionCocycles.frameTransitionValue (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (hl i j) (f i))
        (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (hr i j) (f j))) :
    Nonempty (M ≅ N) := by
  let c (i : ι) : M.over (U i) ≅ N.over (U i) :=
    SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M (U i) (e i) ≪≫
      (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso N (U i) (f i)).symm
  have hc (i j : ι) : SheafCohomology.Projective.LinearHom.linearHomRestrict X.ringCatSheaf M N (homOfLE (hl i j)).op (c i).hom =
      SheafCohomology.Projective.LinearHom.linearHomRestrict X.ringCatSheaf M N (homOfLE (hr i j)).op (c j).hom := by
    have h := OverFrameComparisons.overFrameComparison_eq_of_transition (W i j)
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (hl i j) (e i))
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (hr i j) (e j))
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (hl i j) (f i))
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (hr i j) (f j)) (ht i j)
    exact (OverFrameComparisons.linearHomRestrict_nativeFrameComparison (hl i j) (e i) (f i)).trans
      (h.trans (OverFrameComparisons.linearHomRestrict_nativeFrameComparison (hr i j) (e j) (f j)).symm)
  obtain ⟨g, _⟩ := Local.ModuleIsoGluing.exists_moduleIso_of_overlap_localIsos M N U hU W hl hr hW c hc
  exact ⟨g⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatchingFrameSystems
