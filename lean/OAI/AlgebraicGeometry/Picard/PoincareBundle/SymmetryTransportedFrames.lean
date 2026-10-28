import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.SymmetryFibers

/-! # Symmetry Transported Frames -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SymmetryTransportedFrames

noncomputable section

/-! Naturality of a global pullback frame transported through an actual line symmetry. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.FramePullbackComposition

variable {S : Scheme.{u}} {K J E : Over S} (p : K ⟶ E) (L : Line.Bundles.LineBundle E.left)
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule K.left ≅ (Scheme.Modules.pullback p.left).obj L.sheaf)

theorem evaluation_eq {T : Over S} (a : T ⟶ K) (x : T ⟶ E) (ha : a ≫ p = x) :
    GlobalPullbackFrame.atPoint p L s a x ha = FrameRatioPullback.pullFrame a.left s ≪≫ Line.Fibers.fiberPullbackIso L a p x ha := by
  rw [GlobalPullbackFrame.atPoint, GlobalPullbackFrame.comparison_eq]
  rfl

variable (g : E ⟶ E) (σ : (Scheme.Modules.pullback g.left).obj L.sheaf ≅ L.sheaf)
  (r : J ⟶ K) (q : J ⟶ E) (h : r ≫ p = q ≫ g)

/-- Move a global frame through a commuting square and the line symmetry. -/
def transportedFrame : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule J.left ≅ Line.Fibers.fiber L q :=
  GlobalPullbackFrame.atPoint p L s r (q ≫ g) h ≪≫ Line.SymmetryFibers.atPoint L g σ q

/-- The moved frame evaluates naturally on every test scheme. -/
theorem evaluation {T : Over S} (a : T ⟶ J) (k : T ⟶ K) (m : T ⟶ E)
    (ha : a ≫ q = m) (hr : a ≫ r = k) (hk : k ≫ p = m ≫ g) :
    GlobalPullbackFrame.atPoint q L (transportedFrame p L s g σ r q h) a m ha =
      GlobalPullbackFrame.atPoint p L s k (m ≫ g) hk ≪≫ Line.SymmetryFibers.atPoint L g σ m := by
  have hg : a ≫ (q ≫ g) = m ≫ g :=
    (Category.assoc a q g).symm.trans (congrArg (fun v => v ≫ g) ha)
  have hσ := Line.SymmetryFibers.natural L g σ a q m ha hg
  have hf := GlobalFrameNaturality.atPoint_pullback p L s a r (q ≫ g) h k (m ≫ g) hk hr hg
  calc
    GlobalPullbackFrame.atPoint q L (transportedFrame p L s g σ r q h) a m ha =
        FrameRatioPullback.pullFrame a.left (transportedFrame p L s g σ r q h) ≪≫ Line.Fibers.fiberPullbackIso L a q m ha :=
      evaluation_eq q L (transportedFrame p L s g σ r q h) a m ha
    _ = FrameRatioPullback.pullFrame a.left (GlobalPullbackFrame.atPoint p L s r (q ≫ g) h) ≪≫
        ((Scheme.Modules.pullback a.left).mapIso (Line.SymmetryFibers.atPoint L g σ q) ≪≫
          Line.Fibers.fiberPullbackIso L a q m ha) :=
      (congrArg (fun v => v ≪≫ Line.Fibers.fiberPullbackIso L a q m ha)
        (FramePullbackComposition.pullFrame_trans a.left (GlobalPullbackFrame.atPoint p L s r (q ≫ g) h)
          (Line.SymmetryFibers.atPoint L g σ q))).trans (Iso.trans_assoc _ _ _)
    _ = FrameRatioPullback.pullFrame a.left (GlobalPullbackFrame.atPoint p L s r (q ≫ g) h) ≪≫
        (Line.Fibers.fiberPullbackIso L a (q ≫ g) (m ≫ g) hg ≪≫ Line.SymmetryFibers.atPoint L g σ m) :=
      congrArg (fun v => FrameRatioPullback.pullFrame a.left (GlobalPullbackFrame.atPoint p L s r (q ≫ g) h) ≪≫ v) hσ
    _ = GlobalPullbackFrame.atPoint p L s k (m ≫ g) hk ≪≫ Line.SymmetryFibers.atPoint L g σ m :=
      (Iso.trans_assoc _ _ _).symm.trans
        (congrArg (fun v => v ≪≫ Line.SymmetryFibers.atPoint L g σ m) hf)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SymmetryTransportedFrames
