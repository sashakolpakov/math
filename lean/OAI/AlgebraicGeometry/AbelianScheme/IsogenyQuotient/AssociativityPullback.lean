import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TrilinearPullbackDetection

/-! # Associativity Pullback -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativityPullback.Construction

noncomputable section

/-! Associativity of actual bilinear line maps is preserved by
arbitrary geometric pullback, using the trilinear adjunction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback

universe u

set_option backward.isDefEq.respectTransparency false in
theorem lineBilinear_associative_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N P MN NP Q : Y.Modules}
    (hM : Picard.PoincareBundle.Line.Bundles.IsLine M) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N) (hP : Picard.PoincareBundle.Line.Bundles.IsLine P)
    (hMN : Picard.PoincareBundle.Line.Bundles.IsLine MN) (hNP : Picard.PoincareBundle.Line.Bundles.IsLine NP)
    (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap N P NP) (c : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M NP Q)
    (d : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N MN) (e : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap MN P Q)
    (h : ∀ (U : Y.Opens) (m : Γ(M, U)) (n : Γ(N, U)) (p : Γ(P, U)),
      c.app U m (b.app U n p) = e.app U (d.app U m n) p)
    (V : X.Opens) (m : Γ((Scheme.Modules.pullback f).obj M, V))
    (n : Γ((Scheme.Modules.pullback f).obj N, V)) (p : Γ((Scheme.Modules.pullback f).obj P, V)) :
    (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback f hM hNP c).app V m ((Picard.PoincareBundle.Bilinear.BilinearPullback.pullback f hN hP b).app V n p) =
      (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback f hMN hP e).app V ((Picard.PoincareBundle.Bilinear.BilinearPullback.pullback f hM hN d).app V m n) p := by
  have he : TrilinearProducts.Construction.lineBilinearComposeRight (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback f hN hP b) (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback f hM hNP c) =
      TrilinearProducts.Construction.lineBilinearComposeLeft (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback f hM hN d) (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback f hMN hP e) := by
    apply TrilinearPullbackDetection.Construction.trilinear_eq_of_pullback_units f M N P hM hN hP
    intro U x y z
    rw [TrilinearProducts.Construction.lineBilinearComposeRight_app, TrilinearProducts.Construction.lineBilinearComposeLeft_app,
      TrilinearPullbackDetection.Construction.bilinearPullback_app_units, TrilinearPullbackDetection.Construction.bilinearPullback_app_units,
      TrilinearPullbackDetection.Construction.bilinearPullback_app_units, TrilinearPullbackDetection.Construction.bilinearPullback_app_units, h]
  exact congrArg (fun b => b.app V m n p) he

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativityPullback.Construction
