import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.OpenFrames
import OAI.RepresentationTheory.Theta.Geometric.EqualFrameTransitionGluing

/-! # Frame Gluing -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.FrameGluing

noncomputable section

/-! A bundle with the same native transition ratios as a generating
family of sections is isomorphic to the original bundle. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace PolarizationEmbedding

universe u

theorem exists_iso_of_section_transitions {X : Scheme.{u}} (M Q : X.Modules)
    {ι : Type u} (s : ι → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)) (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (hU : ∀ i, U i ≤ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (W : ι → ι → X.Opens) (hl : ∀ i k, W i k ≤ U i) (hr : ∀ i k, W i k ≤ U k)
    (hw : ∀ i k, U i ⊓ U k ≤ W i k)
    (e : ∀ i, Q.restrict (U i).ι ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (U i).toScheme)
    (he : ∀ i k, (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (hl i k) (e i)).hom =
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (hr i k) (e k)).hom ≫
        SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection
          ((X.homOfLE ((hl i k).trans (hU i))).appTop (AbelianModuli.HilbertConstruction.Section.Frames.sectionRatio (s i) (s k)))) :
    Nonempty (Q ≅ M) := by
  let r i k := (X.homOfLE ((hl i k).trans (hU i))).appTop (AbelianModuli.HilbertConstruction.Section.Frames.sectionRatio (s i) (s k))
  apply RepresentationTheory.Theta.Geometric.EqualFrameTransitionGluing.exists_iso_of_equal_frame_transitions Q M U hcover W hl hr hw e
    (fun i => OpenFrames.PolarizationEmbedding.sectionOpenFrame (s i) (U i) (hU i))
    (fun i k => (W i k).topIso.hom (r i k))
  · intro i k
    rw [Iso.hom_inv_id_apply]
    exact he i k
  · intro i k
    rw [OpenFrames.PolarizationEmbedding.sectionOpenFrame_restrict, OpenFrames.PolarizationEmbedding.sectionOpenFrame_restrict, Iso.hom_inv_id_apply]
    exact OpenFrames.PolarizationEmbedding.sectionOpenFrame_transition (s i) (s k) (W i k) _ _

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.FrameGluing
