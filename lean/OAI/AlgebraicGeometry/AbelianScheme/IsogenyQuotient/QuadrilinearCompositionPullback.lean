import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.QuadrilinearPullback
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TrilinearPullbackDetection

/-! # Quadrilinear Composition Pullback -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.QuadrilinearCompositionPullback.Construction

noncomputable section

/-! Four-input products and exchange of their middle inputs commute
with actual geometric pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {M N P Q MN PQ R : Y.Modules}

set_option backward.isDefEq.respectTransparency false in
theorem linePairBilinearCompose_pullback
    (hM : Picard.PoincareBundle.Line.Bundles.IsLine M) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N)
    (hP : Picard.PoincareBundle.Line.Bundles.IsLine P) (hQ : Picard.PoincareBundle.Line.Bundles.IsLine Q)
    (hMN : Picard.PoincareBundle.Line.Bundles.IsLine MN) (hPQ : Picard.PoincareBundle.Line.Bundles.IsLine PQ)
    (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N MN) (c : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap P Q PQ) (d : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap MN PQ R) :
    QuadrilinearPullback.Construction.lineQuadrilinearPullback f hM hN hP hQ (QuadrilinearProducts.Construction.linePairBilinearCompose b c d) =
      QuadrilinearProducts.Construction.linePairBilinearCompose (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback f hM hN b) (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback f hP hQ c) (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback f hMN hPQ d) := by
  apply QuadrilinearPullbackDetection.Construction.quadrilinear_eq_of_pullback_units f M N P Q hM hN hP hQ
  intro U m n p q
  simp only [QuadrilinearPullback.Construction.lineQuadrilinearPullback_app_units, QuadrilinearProducts.Construction.linePairBilinearCompose_app, TrilinearPullbackDetection.Construction.bilinearPullback_app_units]

set_option backward.isDefEq.respectTransparency false in
theorem lineQuadrilinearPullback_swapMiddle
    (hM : Picard.PoincareBundle.Line.Bundles.IsLine M) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N)
    (hP : Picard.PoincareBundle.Line.Bundles.IsLine P) (hQ : Picard.PoincareBundle.Line.Bundles.IsLine Q)
    (b : QuadrilinearProducts.Construction.SheafQuadrilinearMap M N P Q R) :
    QuadrilinearPullback.Construction.lineQuadrilinearPullback f hM hP hN hQ b.swapMiddle =
      (QuadrilinearPullback.Construction.lineQuadrilinearPullback f hM hN hP hQ b).swapMiddle := by
  apply QuadrilinearPullbackDetection.Construction.quadrilinear_eq_of_pullback_units f M P N Q hM hP hN hQ
  intro U m p n q
  simp only [QuadrilinearPullback.Construction.lineQuadrilinearPullback_app_units, QuadrilinearProducts.Construction.SheafQuadrilinearMap.swapMiddle_app]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.QuadrilinearCompositionPullback.Construction
