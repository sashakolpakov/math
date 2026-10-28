import OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalFrameNaturality
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.TransportComposition

/-! # Line Bilinear -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineBilinear

noncomputable section

/-!
# Transport genuine bilinear operations to the fibers of a pulled-back line bundle
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

section

/-- The corresponding inverse square of four actual isomorphisms commutes. -/
theorem inverse_iso_square {C : Type*} [Category C] {A B U V : C}
    (a : A ≅ U) (b : B ≅ V) (c : A ≅ B) (d : U ≅ V) (h : a ≪≫ d = c ≪≫ b) :
    a.symm ≪≫ c = d ≪≫ b.symm := by
  apply Iso.ext
  exact Bilinear.PullbackNaturality.inverse_square a b c.hom d.hom (congrArg Iso.hom h).symm

end

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.TransportComposition

variable {S : Scheme.{u}} {K E : Over S} (p : K ⟶ E) (L : Line.Bundles.LineBundle E.left)

/-- View the actual composition comparison with its pulled-line fiber source explicitly specified. -/
def fiberComparison {T : Over S} (k : T ⟶ K) (a : T ⟶ E) (hk : k ≫ p = a) :
    Line.Fibers.fiber (L.pullback p.left) k ≅ Line.Fibers.fiber L a := GlobalPullbackFrame.comparison p L k a hk

/-- The inverse actual fiber comparisons satisfy the square needed to transport bilinear operations. -/
theorem comparison_inverse_square {T T' : Over S} (g : T' ⟶ T) (k : T ⟶ K) (a : T ⟶ E)
    (hk : k ≫ p = a) (k' : T' ⟶ K) (a' : T' ⟶ E) (hk' : k' ≫ p = a')
    (hgk : g ≫ k = k') (hga : g ≫ a = a') :
    (Scheme.Modules.pullback g.left).mapIso (fiberComparison p L k a hk).symm ≪≫
      Line.Fibers.fiberPullbackIso (L.pullback p.left) g k k' hgk =
    Line.Fibers.fiberPullbackIso L g a a' hga ≪≫ (fiberComparison p L k' a' hk').symm :=
  inverse_iso_square _ _ _ _ (GlobalFrameNaturality.comparison_pullback p L g k a hk k' a' hk' hgk hga)

/-- Transport an actual bilinear operation of original fibers to the corresponding pulled-back line fibers. -/
def transport {T : Over S} (x y z : T ⟶ K) (a b c : T ⟶ E)
    (hx : x ≫ p = a) (hy : y ≫ p = b) (hz : z ≫ p = c)
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber L a) (Line.Fibers.fiber L b) (Line.Fibers.fiber L c)) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber (L.pullback p.left) x) (Line.Fibers.fiber (L.pullback p.left) y) (Line.Fibers.fiber (L.pullback p.left) z) :=
  Bilinear.Transport.transport β (fiberComparison p L x a hx).symm (fiberComparison p L y b hy).symm
    (fiberComparison p L z c hz).symm

/-- The transported genuine fiber-bilinear operation has the full geometric pullback compatibility. -/
theorem transport_pullback {T T' : Over S} (g : T' ⟶ T)
    (x y z : T ⟶ K) (a b c : T ⟶ E) (hx : x ≫ p = a) (hy : y ≫ p = b) (hz : z ≫ p = c)
    (x' y' z' : T' ⟶ K) (a' b' c' : T' ⟶ E)
    (hx' : x' ≫ p = a') (hy' : y' ≫ p = b') (hz' : z' ≫ p = c')
    (hgx : g ≫ x = x') (hgy : g ≫ y = y') (hgz : g ≫ z = z')
    (hga : g ≫ a = a') (hgb : g ≫ b = b') (hgc : g ≫ c = c')
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber L a) (Line.Fibers.fiber L b) (Line.Fibers.fiber L c)) :
    Line.Fibers.pullBilinear (L.pullback p.left) g x y z x' y' z' hgx hgy hgz (transport p L x y z a b c hx hy hz β) =
      transport p L x' y' z' a' b' c' hx' hy' hz' (Line.Fibers.pullBilinear L g a b c a' b' c' hga hgb hgc β) := by
  unfold transport Line.Fibers.pullBilinear
  rw [Bilinear.TransportComposition.pullback_transport g.left (Line.Fibers.fiber_isLine L a) (Line.Fibers.fiber_isLine L b)
    (Line.Fibers.fiber_isLine (L.pullback p.left) x) (Line.Fibers.fiber_isLine (L.pullback p.left) y) β
    (fiberComparison p L x a hx).symm (fiberComparison p L y b hy).symm (fiberComparison p L z c hz).symm,
    Bilinear.TransportComposition.transport_trans,
    comparison_inverse_square p L g x a hx x' a' hx' hgx hga,
    comparison_inverse_square p L g y b hy y' b' hy' hgy hgb,
    comparison_inverse_square p L g z c hz z' c' hz' hgz hgc,
    ← Bilinear.TransportComposition.transport_trans]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineBilinear
