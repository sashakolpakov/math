import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FramePullbackComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Classification

/-! # Frame At Point -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.FrameAtPoint

noncomputable section

/-! Local frames give coherent frames at a point which factors through
their open sets. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {W X Y Z : Scheme.{u}}

theorem pullbackCongr_refl_app (a : X ⟶ Y) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr (rfl : a = a)).app M = Iso.refl ((Scheme.Modules.pullback a).obj M) := rfl

def frameAtPoint (a : X ⟶ Y) (b : Y ⟶ Z) (p : X ⟶ Z) (h : a ≫ b = p)
    {M : Z.Modules} (e : (Scheme.Modules.pullback b).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) :
    (Scheme.Modules.pullback p).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X :=
  (Scheme.Modules.pullbackCongr h.symm).app M ≪≫ FramePullbackComposition.refineFrame a b e

theorem frameAtPoint_refinement (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
    (v : X ⟶ Z) (p : W ⟶ Z) (t : W ⟶ Y)
    (hv : b ≫ c = v) (ha : a ≫ v = p) (ht : t ≫ c = p) (hab : a ≫ b = t)
    {M : Z.Modules} (e : (Scheme.Modules.pullback c).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) :
    frameAtPoint a v p ha ((Scheme.Modules.pullbackCongr hv.symm).app M ≪≫ FramePullbackComposition.refineFrame b c e) =
      frameAtPoint t c p ht e := by
  subst v
  subst t
  subst p
  simpa only [frameAtPoint, pullbackCongr_refl_app, Iso.refl_trans] using FramePullbackComposition.refineFrame_assoc a b c e

theorem restrictFrame_eq {M : Z.Modules} {U V : Z.Opens} (hVU : V ≤ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) :
    Picard.PoincareBundle.Affine.Classification.restrictTrivialization M hVU e =
      frameAtPoint (Z.homOfLE hVU) U.ι V.ι (Z.homOfLE_ι hVU) e := by
  apply Iso.ext
  rfl

theorem frameAtPoint_restrict {M : Z.Modules} {U V : Z.Opens} (hVU : V ≤ U)
    (a : W ⟶ V.toScheme) (t : W ⟶ U.toScheme) (p : W ⟶ Z)
    (ha : a ≫ V.ι = p) (ht : t ≫ U.ι = p)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) :
    frameAtPoint a V.ι p ha (Picard.PoincareBundle.Affine.Classification.restrictTrivialization M hVU e) =
      frameAtPoint t U.ι p ht e := by
  rw [restrictFrame_eq]
  have hat : a ≫ Z.homOfLE hVU = t := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, Z.homOfLE_ι, ha, ht]
  exact frameAtPoint_refinement a (Z.homOfLE hVU) U.ι V.ι p t (Z.homOfLE_ι hVU) ha ht hat e

theorem frameTransitionValue_frameAtPoint (a : X ⟶ Y) (b : Y ⟶ Z) (p : X ⟶ Z) (h : a ≫ b = p)
    {M : Z.Modules} (e f : (Scheme.Modules.pullback b).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) :
    FrameTransitionCocycles.frameTransitionValue (frameAtPoint a b p h e) (frameAtPoint a b p h f) =
      a.appTop (FrameTransitionCocycles.frameTransitionValue e f) := by
  simp only [frameAtPoint, FramePullbackComposition.refineFrame, FrameTransitionCocycles.frameTransitionValue_change_source, FrameTransitionPullback.frameTransitionValue_pullback]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.FrameAtPoint
