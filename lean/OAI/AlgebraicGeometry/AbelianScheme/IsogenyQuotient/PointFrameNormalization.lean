import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PointFrameSection

/-! # Point Frame Normalization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PointFrameNormalization.Construction

noncomputable section

/-! A point-frame equality gives the exact normalized pullback of the
global frame, including the unit and fiber comparison isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame

universe u

theorem atPoint_pullback_of_eq {S : Scheme.{u}} {A E T : Over S} (p : A ⟶ E)
    (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ≅ (Scheme.Modules.pullback p.left).obj L.sheaf)
    (a : T ⟶ A) (x : T ⟶ E) (hx : a ≫ p = x)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Picard.PoincareBundle.Line.Fibers.fiber L x) (h : Picard.PoincareBundle.GlobalPullbackFrame.atPoint p L s a x hx = z) :
    (Scheme.Modules.pullback a.left).mapIso s =
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso a.left ≪≫ z ≪≫ (Picard.PoincareBundle.GlobalPullbackFrame.comparison p L a x hx).symm := by
  rw [← h]
  simp only [Picard.PoincareBundle.GlobalPullbackFrame.atPoint, Picard.PoincareBundle.FrameRatioPullback.pullFrame, Iso.trans_assoc,
    Iso.self_symm_id_assoc, Iso.self_symm_id, Iso.trans_refl]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PointFrameNormalization.Construction
