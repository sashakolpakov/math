import OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame

/-! # Global Frame Naturality -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalFrameNaturality

noncomputable section

/-!
# Frames obtained from a global pullback trivialization are natural on all test schemes
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.FramePullbackComposition

variable {S : Scheme.{u}} {K E : Over S} (p : K ⟶ E) (L : Line.Bundles.LineBundle E.left)

/-- The actual fiber comparisons commute with geometric pullback in their entire isomorphism square. -/
theorem comparison_pullback {T T' : Over S} (a : T' ⟶ T) (k : T ⟶ K) (x : T ⟶ E)
    (hk : k ≫ p = x) (k' : T' ⟶ K) (x' : T' ⟶ E) (hk' : k' ≫ p = x')
    (hak : a ≫ k = k') (hax : a ≫ x = x') :
    (Scheme.Modules.pullback a.left).mapIso (GlobalPullbackFrame.comparison p L k x hk) ≪≫ Line.Fibers.fiberPullbackIso L a x x' hax =
      Line.Fibers.fiberPullbackIso (L.pullback p.left) a k k' hak ≪≫ GlobalPullbackFrame.comparison p L k' x' hk' := by
  have hn := PullbackFiberComposition.fiberIsoTo_hom_pullback (Geometric.KernelLinearization.overModulePullbacks S)
    p L.sheaf a k x hk k' x' hk' hak hax
  have hr := DescentReindexing.pullHom_reindex (Over.forget S) Geometric.KernelLinearization.modulePullbacks
    (GlobalPullbackFrame.comparison p L k x hk).hom a k' x' hak hax
  have hf := Geometric.PullHom.pullHom_eq (GlobalPullbackFrame.comparison p L k x hk).hom a.left k'.left x'.left
    (congrArg Over.Hom.left hak) (congrArg Over.Hom.left hax)
  have hs : (Line.Fibers.fiberPullbackIso (L.pullback p.left) a k k' hak).inv ≫
      (Scheme.Modules.pullback a.left).map (GlobalPullbackFrame.comparison p L k x hk).hom ≫
        (Line.Fibers.fiberPullbackIso L a x x' hax).hom = (GlobalPullbackFrame.comparison p L k' x' hk').hom :=
    (hr.trans hf).symm.trans hn
  apply Iso.ext
  apply (cancel_epi (Line.Fibers.fiberPullbackIso (L.pullback p.left) a k k' hak).inv).mp
  change (Line.Fibers.fiberPullbackIso (L.pullback p.left) a k k' hak).inv ≫
      (Scheme.Modules.pullback a.left).map (GlobalPullbackFrame.comparison p L k x hk).hom ≫
        (Line.Fibers.fiberPullbackIso L a x x' hax).hom =
    (Line.Fibers.fiberPullbackIso (L.pullback p.left) a k k' hak).inv ≫
      (Line.Fibers.fiberPullbackIso (L.pullback p.left) a k k' hak).hom ≫ (GlobalPullbackFrame.comparison p L k' x' hk').hom
  exact hs.trans (Iso.inv_hom_id_assoc (Line.Fibers.fiberPullbackIso (L.pullback p.left) a k k' hak)
    (GlobalPullbackFrame.comparison p L k' x' hk').hom).symm

variable (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule K.left ≅ (Scheme.Modules.pullback p.left).obj L.sheaf)

/-- Canonical pullback of the global frame is coherent with the specified lifted test point. -/
theorem pulledFrame_lift {T T' : Over S} (a : T' ⟶ T) (k : T ⟶ K) (k' : T' ⟶ K) (hak : a ≫ k = k') :
    FrameRatioPullback.pullFrame a.left (FrameRatioPullback.pullFrame k.left s) ≪≫ Line.Fibers.fiberPullbackIso (L.pullback p.left) a k k' hak =
      FrameRatioPullback.pullFrame k'.left s := by
  change FrameRatioPullback.pullFrame a.left (FrameRatioPullback.pullFrame k.left s) ≪≫
    ((Scheme.Modules.pullbackComp a.left k.left).app ((Scheme.Modules.pullback p.left).obj L.sheaf) ≪≫
      (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hak)).app ((Scheme.Modules.pullback p.left).obj L.sheaf)) = _
  rw [← Iso.trans_assoc, FramePullbackComposition.pullFrame_comp]
  exact FramePullbackComposition.pullFrame_congr (a.left ≫ k.left) s k'.left (congrArg Over.Hom.left hak)

/-- The entire frame at the new test point is the canonical pullback of the original frame. -/
theorem atPoint_pullback {T T' : Over S} (a : T' ⟶ T) (k : T ⟶ K) (x : T ⟶ E)
    (hk : k ≫ p = x) (k' : T' ⟶ K) (x' : T' ⟶ E) (hk' : k' ≫ p = x')
    (hak : a ≫ k = k') (hax : a ≫ x = x') :
    FrameRatioPullback.pullFrame a.left (GlobalPullbackFrame.atPoint p L s k x hk) ≪≫ Line.Fibers.fiberPullbackIso L a x x' hax = GlobalPullbackFrame.atPoint p L s k' x' hk' := by
  unfold GlobalPullbackFrame.atPoint
  rw [FramePullbackComposition.pullFrame_trans, Iso.trans_assoc, comparison_pullback p L a k x hk k' x' hk' hak hax]
  have h := congrArg (fun e => e ≪≫ GlobalPullbackFrame.comparison p L k' x' hk') (pulledFrame_lift p L s a k k' hak)
  exact (Iso.trans_assoc _ _ _).symm.trans h

/-- The normalized section of the constructed fiber frame has the required genuine geometric naturality. -/
theorem atPoint_section_natural {T T' : Over S} (a : T' ⟶ T) (k : T ⟶ K) (x : T ⟶ E)
    (hk : k ≫ p = x) (k' : T' ⟶ K) (x' : T' ⟶ E) (hk' : k' ≫ p = x')
    (hak : a ≫ k = k') (hax : a ≫ x = x') :
    Line.Fibers.pullSection L a x x' hax (GlobalPullbackFrame.atPoint p L s k x hk).hom = (GlobalPullbackFrame.atPoint p L s k' x' hk').hom :=
  congrArg Iso.hom (atPoint_pullback p L s a k x hk k' x' hk' hak hax)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalFrameNaturality
