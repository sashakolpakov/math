import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FrameAtPoint
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenPullbackFrame

/-! # Frame Restriction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.FrameRestriction

noncomputable section

/-! Presentations pullback frames and native open-restriction frames agree
under restriction to smaller opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X : Scheme.{u}} {M : X.Modules}

def nativeOpenFrame (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) :
    M.restrict U.ι ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme :=
  (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫ e

theorem nativeOpenFrame_restrict {U V : X.Opens} (h : V ≤ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) :
    SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h (nativeOpenFrame U e) =
      nativeOpenFrame V (Picard.PoincareBundle.Affine.Classification.restrictTrivialization M h e) := by
  erw [SheafCohomology.Projective.OpenPullbackFrame.Scheme.Modules.restrictOpenTrivialization_eq_pullback]
  have he : ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M) ≪≫ nativeOpenFrame U e = e := by
    apply Iso.ext
    change ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).inv ≫
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).hom ≫ e.hom = e.hom
    exact ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).inv_hom_id_assoc _
  change (Scheme.Modules.restrictFunctorIsoPullback V.ι).app M ≪≫
    SheafCohomology.Projective.Invertible.Scheme.Modules.restrictTrivialization h
      (((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M) ≪≫ nativeOpenFrame U e) = _
  erw [he]
  apply Iso.ext
  rfl

theorem nativeOpenFrame_transition (U : X.Opens)
    (e f : (Scheme.Modules.pullback U.ι).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) :
    FrameTransitionCocycles.frameTransitionValue (nativeOpenFrame U e) (nativeOpenFrame U f) = FrameTransitionCocycles.frameTransitionValue e f :=
  FrameTransitionCocycles.frameTransitionValue_change_source ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M) e f

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.FrameRestriction
